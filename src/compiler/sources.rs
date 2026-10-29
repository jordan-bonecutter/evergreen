//! Resolve bundled standard-library dependencies without filesystem searches.
//! Each input keeps its own line numbers. Loaded library bytes bind certificates.

use crate::syntax::{
    self, Expr, Function, GenericArgument, GenericDeclaration, Kind, Program, Statement, Struct,
    Type,
};
use std::collections::{BTreeMap, BTreeSet};

type Result<T> = std::result::Result<T, String>;

struct Library {
    module: Option<&'static str>,
    exports: &'static [&'static str],
    path: &'static str,
    source: &'static str,
}

const LIBRARIES: &[Library] = &[
    Library {
        module: Some("integer"),
        exports: &[],
        path: "stdlib/integer/integer.evg",
        source: include_str!("../../stdlib/integer/integer.evg"),
    },
    Library {
        module: Some("nat"),
        exports: &[],
        path: "stdlib/nat/nat.evg",
        source: include_str!("../../stdlib/nat/nat.evg"),
    },
    Library {
        module: Some("usize"),
        exports: &[],
        path: "stdlib/usize/usize.evg",
        source: include_str!("../../stdlib/usize/usize.evg"),
    },
    Library {
        module: Some("console"),
        exports: &[],
        path: "stdlib/console/console.evg",
        source: include_str!("../../stdlib/console/console.evg"),
    },
    Library {
        module: Some("rc"),
        exports: &[],
        path: "stdlib/rc/rc.evg",
        source: include_str!("../../stdlib/rc/rc.evg"),
    },
    Library {
        module: Some("allocation_credits"),
        exports: &[],
        path: "stdlib/allocation_credits/allocation_credits.evg",
        source: include_str!("../../stdlib/allocation_credits/allocation_credits.evg"),
    },
    Library {
        module: Some("utf8"),
        exports: &[],
        path: "stdlib/utf8/utf8.evg",
        source: include_str!("../../stdlib/utf8/utf8.evg"),
    },
    Library {
        module: Some("vec"),
        exports: &[],
        path: "stdlib/vec/vec.evg",
        source: include_str!("../../stdlib/vec/vec.evg"),
    },
    Library {
        module: Some("linux_io"),
        exports: &[],
        path: "stdlib/linux_io/linux_io.evg",
        source: include_str!("../../stdlib/linux_io/linux_io.evg"),
    },
    Library {
        module: Some("x86_64_atomics"),
        exports: &[],
        path: "stdlib/x86_64_atomics/x86_64_atomics.evg",
        source: include_str!("../../stdlib/x86_64_atomics/x86_64_atomics.evg"),
    },
    Library {
        module: Some("atomic_counter"),
        exports: &[],
        path: "stdlib/atomic_counter/atomic_counter.evg",
        source: include_str!("../../stdlib/atomic_counter/atomic_counter.evg"),
    },
    Library {
        module: Some("credits"),
        exports: &[],
        path: "stdlib/credits/credits.evg",
        source: include_str!("../../stdlib/credits/credits.evg"),
    },
    Library {
        module: Some("borrow_credits"),
        exports: &[],
        path: "stdlib/borrow_credits/borrow_credits.evg",
        source: include_str!("../../stdlib/borrow_credits/borrow_credits.evg"),
    },
    Library {
        module: Some("arrays"),
        exports: &[],
        path: "stdlib/arrays/array.evg",
        source: include_str!("../../stdlib/arrays/array.evg"),
    },
    Library {
        module: Some("arrays"),
        exports: &[],
        path: "stdlib/arrays/fill.evg",
        source: include_str!("../../stdlib/arrays/fill.evg"),
    },
    Library {
        module: Some("arrays"),
        exports: &[],
        path: "stdlib/arrays/copy.evg",
        source: include_str!("../../stdlib/arrays/copy.evg"),
    },
    Library {
        module: Some("arrays"),
        exports: &[],
        path: "stdlib/arrays/release.evg",
        source: include_str!("../../stdlib/arrays/release.evg"),
    },
    Library {
        module: Some("arrays"),
        exports: &[],
        path: "stdlib/arrays/prefix.evg",
        source: include_str!("../../stdlib/arrays/prefix.evg"),
    },
    Library {
        module: None,
        exports: &["swap_usize", "swap_bool"],
        path: "stdlib/swap.evg",
        source: include_str!("../../stdlib/swap.evg"),
    },
    Library {
        module: None,
        exports: &[
            "counter_increment",
            "counter_try_increment",
            "counter_decrement",
            "counter_roundtrip",
        ],
        path: "stdlib/counter.evg",
        source: include_str!("../../stdlib/counter.evg"),
    },
];

pub(super) struct Loaded {
    pub program: Program,
    pub fingerprint: String,
}

#[derive(Clone, Default)]
struct Names(BTreeSet<String>);

impl Names {
    fn ty(&mut self, ty: &Type) {
        match ty {
            Type::Apply(name, arguments) => {
                self.0.insert(name.clone());
                self.arguments(arguments);
            }
            Type::Named(name) => {
                self.0.insert(name.clone());
            }
            Type::Ref(inner) | Type::Unique(inner) | Type::Shared(inner) | Type::Shape(inner) => {
                self.ty(inner)
            }
            Type::Union(members) => {
                for member in members {
                    self.ty(member);
                }
            }
            Type::Array(inner, extent) => {
                self.ty(inner);
                self.expr(extent);
            }
            _ => {}
        }
    }

    fn expr(&mut self, e: &Expr) {
        match &e.kind {
            Kind::Forall { domain, body, .. } => {
                self.expr(domain);
                self.expr(body);
            }
            Kind::Type(ty) => self.ty(ty),
            Kind::Generic {
                arguments, value, ..
            } => {
                self.arguments(arguments);
                self.expr(value);
            }
            Kind::Call(name, values) => {
                self.0.insert(name.clone());
                for value in values {
                    self.expr(value);
                }
            }
            Kind::Record(name, fields) => {
                self.0.insert(name.clone());
                for (_, value) in fields {
                    self.expr(value);
                }
            }
            Kind::Unary(_, e) | Kind::Field(e, _) | Kind::FactAt(e, _) => self.expr(e),
            Kind::Binary(_, a, b) | Kind::Index(a, b) => {
                self.expr(a);
                self.expr(b);
            }
            Kind::If(c, a, b) => {
                self.expr(c);
                self.expr(a);
                self.expr(b);
            }
            Kind::Block(body, tail) => {
                for statement in body {
                    self.statement(statement);
                }
                self.expr(tail);
            }
            Kind::Array(values) => {
                for value in values {
                    self.expr(value);
                }
            }
            _ => {}
        }
    }

    fn arguments(&mut self, arguments: &[GenericArgument]) {
        for argument in arguments {
            match argument {
                GenericArgument::Type(ty) => self.ty(ty),
                GenericArgument::Const(value) => self.expr(value),
            }
        }
    }

    fn generic(&mut self, declaration: &GenericDeclaration) {
        let parameters = declaration.parameters();
        for parameter in parameters {
            match parameter {
                syntax::GenericParameter::Type { default, .. } => {
                    if let Some(ty) = default {
                        self.ty(ty);
                    }
                }
                syntax::GenericParameter::Const { ty, default, .. } => {
                    self.ty(ty);
                    if let Some(value) = default {
                        self.expr(value);
                    }
                }
            }
        }
        match declaration {
            GenericDeclaration::Implementation(implementation) => {
                self.ty(&implementation.target);
                for function in &implementation.functions {
                    self.function(function);
                }
            }
            GenericDeclaration::Record { definition, .. } => self.structure(definition),
            GenericDeclaration::Function { definition, .. } => self.function(definition),
        }
    }

    fn statement(&mut self, statement: &Statement) {
        match statement {
            Statement::Ideal(s) => self.statement(s),
            Statement::Let { ty, value, .. } => {
                if let Some(ty) = ty {
                    self.ty(ty);
                }
                self.expr(value);
            }
            Statement::Destructure {
                record,
                arguments,
                value,
                ..
            } => {
                self.arguments(arguments);
                self.0.insert(record.clone());
                self.expr(value);
            }
            Statement::Fact { value, .. } | Statement::Effect(value) => self.expr(value),
            Statement::Proof { proposition, .. } => self.expr(proposition),
            Statement::Assign {
                target,
                value,
                starts,
            } => {
                self.expr(target);
                self.expr(value);
                for source in starts {
                    self.expr(source);
                }
            }
            Statement::While {
                condition,
                invariant,
                modifies,
                decreases,
                body,
                ..
            } => {
                self.expr(condition);
                self.expr(invariant);
                if let Some(measure) = decreases {
                    self.expr(measure);
                }
                for effect in modifies {
                    self.expr(effect);
                }
                for item in body {
                    self.statement(item);
                }
            }
            Statement::Update { places, body, .. } => {
                for e in places {
                    self.expr(e);
                }
                for s in body {
                    self.statement(s);
                }
            }
        }
    }

    fn function(&mut self, function: &Function) {
        for (_, ty) in &function.params {
            self.ty(ty);
        }
        self.ty(&function.ret);
        for e in [&function.pre, &function.post, &function.decreases]
            .into_iter()
            .flatten()
        {
            self.expr(e);
        }
        for e in &function.modifies {
            self.expr(e);
        }
        for borrow in &function.borrows {
            self.expr(&borrow.reference);
        }
        for s in &function.body {
            self.statement(s);
        }
        self.expr(&function.result);
    }

    fn structure(&mut self, structure: &Struct) {
        for (_, ty) in &structure.fields {
            self.ty(ty);
        }
        for (_, e) in &structure.facts {
            self.expr(e);
        }
        if let Some(e) = &structure.invariant {
            self.expr(e);
        }
    }
}

struct Loader {
    supplied_modules: BTreeSet<String>,
    supplied_functions: BTreeSet<String>,
    type_dependencies: BTreeMap<String, Names>,
    parsed: Vec<Option<Program>>,
    structures: BTreeSet<usize>,
    functions: BTreeSet<usize>,
    output: Loaded,
}

impl Loader {
    fn needed(&self, mut names: Names) -> Vec<usize> {
        // Constructors and owned parameters may invoke a destructor implicitly.
        // Bring its library helpers into scope before that user function too.
        let mut pending = names.0.iter().cloned().collect::<Vec<_>>();
        let mut visited = BTreeSet::new();
        while let Some(name) = pending.pop() {
            if !visited.insert(name.clone()) {
                continue;
            }
            if let Some(dependencies) = self.type_dependencies.get(&name) {
                for dependency in &dependencies.0 {
                    if names.0.insert(dependency.clone()) {
                        pending.push(dependency.clone());
                    }
                }
            }
        }
        LIBRARIES
            .iter()
            .enumerate()
            .filter_map(|(index, library)| {
                if let Some(module) = library.module {
                    if self.supplied_modules.contains(module) {
                        return None;
                    }
                    if names.0.iter().any(|name| {
                        name.split_once("::")
                            .is_some_and(|(prefix, _)| prefix == module)
                    }) {
                        return Some(index);
                    }
                } else if library
                    .exports
                    .iter()
                    .any(|name| names.0.contains(*name) && !self.supplied_functions.contains(*name))
                {
                    return Some(index);
                }
                None
            })
            .collect()
    }

    fn library(&mut self, index: usize) -> Result<Program> {
        if self.parsed[index].is_none() {
            let library = &LIBRARIES[index];
            if self.output.fingerprint.len() + library.source.len() + library.path.len() + 32
                > 1_000_000
            {
                return Err(
                    "source and standard-library dependencies exceed 1 MB bootstrap limit".into(),
                );
            }
            let mut program = syntax::parse(library.source)
                .map_err(|error| format!("{}: {error}", library.path))?;
            program.set_source_origin(crate::shared::diagnostics::SourceOrigin::Bundled(
                library.path,
            ));
            self.output
                .fingerprint
                .push_str(&format!("\n// bundled {}\n", library.path));
            self.output.fingerprint.push_str(library.source);
            self.output
                .program
                .modules
                .extend(program.modules.iter().cloned());
            self.parsed[index] = Some(program);
        }
        Ok(self.parsed[index].as_ref().unwrap().clone())
    }

    fn dependencies(&self, program: &Program) -> Vec<usize> {
        let mut names = Names::default();
        for declaration in &program.generics {
            names.generic(declaration);
        }
        for structure in &program.structs {
            names.structure(structure);
        }
        for function in &program.functions {
            names.function(function);
        }
        self.needed(names)
    }

    fn structures(&mut self, index: usize) -> Result<()> {
        if !self.structures.insert(index) {
            return Ok(());
        }
        let program = self.library(index)?;
        for dependency in self.dependencies(&program) {
            if dependency != index {
                self.structures(dependency)?;
            }
        }
        self.output.program.copy_impls.extend(program.copy_impls);
        self.output.program.generics.extend(program.generics);
        self.output
            .program
            .scalar_types
            .extend(program.scalar_types);
        self.output.program.structs.extend(program.structs);
        Ok(())
    }

    fn functions(&mut self, index: usize) -> Result<()> {
        if !self.functions.insert(index) {
            return Ok(());
        }
        self.structures(index)?;
        let program = self.library(index)?;
        for dependency in self.dependencies(&program) {
            if dependency != index {
                self.functions(dependency)?;
            }
        }
        self.output.program.functions.extend(
            program
                .functions
                .into_iter()
                .filter(|function| !self.supplied_functions.contains(&function.name)),
        );
        self.output.program.destructors.extend(program.destructors);
        Ok(())
    }
}

pub(super) fn load(source: &str) -> Result<Loaded> {
    crate::shared::worker::run("evergreen-source-loader", || {
        let user = syntax::parse(source)?;
        for import in &user.imports {
            if !user.modules.contains(import) && !is_bundled_module(import) {
                return Err(format!("unresolved import {import}; load its package directory or provide its source units"));
            }
        }
        let supplied_modules = user.modules.clone();
        let supplied_functions = user.functions.iter().map(|f| f.name.clone()).collect();
        let mut type_dependencies = BTreeMap::<String, Names>::new();
        for structure in &user.structs {
            type_dependencies
                .entry(structure.name.clone())
                .or_default()
                .structure(structure);
        }
        for (target, method) in &user.destructors {
            type_dependencies
                .entry(target.clone())
                .or_default()
                .function(method);
        }
        let mut loader = Loader {
            supplied_modules,
            supplied_functions,
            type_dependencies,
            parsed: vec![None; LIBRARIES.len()],
            structures: BTreeSet::new(),
            functions: BTreeSet::new(),
            output: Loaded {
                program: Program {
                    generics: Vec::new(),
                    copy_impls: user.copy_impls,
                    imports: user.imports,
                    scalar_types: user.scalar_types,
                    structs: Vec::new(),
                    functions: Vec::new(),
                    destructors: Vec::new(),
                    modules: user.modules,
                },
                fingerprint: source.into(),
            },
        };
        for declaration in user.generics {
            let mut names = Names::default();
            names.generic(&declaration);
            for index in loader.needed(names) {
                loader.functions(index)?;
            }
            loader.output.program.generics.push(declaration);
        }
        for structure in user.structs {
            let mut names = Names::default();
            names.structure(&structure);
            for index in loader.needed(names) {
                loader.structures(index)?;
            }
            loader.output.program.structs.push(structure);
        }
        for function in user.functions {
            let mut names = Names::default();
            names.function(&function);
            for index in loader.needed(names) {
                loader.functions(index)?;
            }
            loader.output.program.functions.push(function);
        }
        for (name, method) in user.destructors {
            let mut names = Names::default();
            names.function(&method);
            for index in loader.needed(names) {
                loader.functions(index)?;
            }
            loader.output.program.destructors.push((name, method));
        }
        Ok(loader.output)
    })
}

pub(super) fn is_bundled_module(name: &str) -> bool {
    LIBRARIES.iter().any(|library| library.module == Some(name))
}

/// Embedded source for diagnostics; no filesystem lookup is performed.
pub(super) fn bundled_source(path: &str) -> Option<&'static str> {
    LIBRARIES
        .iter()
        .find(|library| library.path == path)
        .map(|library| library.source)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler::verify::{prove, verify, verify_with_certificate};

    #[test]
    fn standard_library_is_automatic_and_transitive_but_not_a_blanket_prelude() {
        let source = include_str!("../../examples/hello.evg");
        let (program, bundle) = prove(source).unwrap();
        assert_eq!(program.trusted_assumptions().len(), 1);
        assert_eq!(
            verify_with_certificate(source, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
        let loaded = load(source).unwrap();
        assert!(loaded.program.modules.contains("linux_io"));
        assert!(loaded
            .fingerprint
            .contains("// bundled stdlib/linux_io/linux_io.evg"));
        assert!(bundle.check_source(source).is_err());
        assert!(bundle.check_source(&loaded.fingerprint).is_ok());
        let counter = verify(include_str!("../../examples/atomic_counter.evg")).unwrap();
        assert_eq!(counter.trusted_assumptions().len(), 1);
        assert_eq!(counter.run().unwrap().to_string(), "42");
        let plain = verify("fn main() -> usize {42}").unwrap();
        assert!(plain.trusted_assumptions().is_empty());
        assert_eq!(
            load("fn main() -> usize {42}").unwrap().fingerprint,
            "fn main() -> usize {42}"
        );
        let flat =
            verify("fn main() -> usize {let count: usize = 41; counter_increment(&count); count}")
                .unwrap();
        assert_eq!(flat.run().unwrap().to_string(), "42");
    }

    #[test]
    fn primitive_type_observations_do_not_load_word_policy_libraries() {
        let source =
            "fn main() -> usize {let value = usize::MAX; proof _: typeof(value) == usize; 42}";
        assert_eq!(load(source).unwrap().fingerprint, source);
        let source = "fn main() {proof _: integer::from(42) == 42;}";
        let loaded = load(source).unwrap();
        assert!(loaded.program.modules.contains("integer"));
        assert!(!loaded.program.modules.contains("usize"));
        assert!(!loaded.program.modules.contains("nat"));
    }

    #[test]
    fn explicit_modules_are_not_loaded_twice_and_user_lines_are_preserved() {
        let explicit = [
            include_str!("../../stdlib/linux_io/linux_io.evg"),
            include_str!("../../examples/hello.evg"),
        ]
        .join("\n");
        let program = verify(&explicit).unwrap();
        assert_eq!(program.trusted_assumptions().len(), 1);
        assert_eq!(load(&explicit).unwrap().fingerprint, explicit);
        let error =
            verify("fn main() -> usize {\n let n: usize = 0;\n linux_io::does_not_exist()\n}")
                .unwrap_err();
        assert!(
            error.contains("line 3: unknown function linux_io::does_not_exist"),
            "{error}"
        );
        assert!(!error.contains("recursion"), "{error}");
        let drop_helper = "type Pair struct {a: &usize, b: &usize} impl Drop for Pair {fn drop(self) modifies(self.a, self.b) {swap_usize(self.a, self.b);}} fn main() -> usize {let a: usize = 7; let b: usize = 42; let pair = Pair {a: &a, b: &b}; drop(pair); a}";
        assert_eq!(
            verify(drop_helper).unwrap().run().unwrap().to_string(),
            "42"
        );
        let recursion = verify("ideal fn recurse(n: nat) -> nat {recurse(n)}").unwrap_err();
        assert!(
            recursion.contains("recursive ideal function recurse requires a decreases clause"),
            "{recursion}"
        );
    }
}
