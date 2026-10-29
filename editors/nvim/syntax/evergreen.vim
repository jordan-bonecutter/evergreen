if exists('b:current_syntax')
  finish
endif

syntax keyword evergreenDeclaration fn method type struct impl module import extern
syntax keyword evergreenKeyword let pub for with self Self return if else while
syntax keyword evergreenContract where ensures borrows modifies decreases lifts update invariant
syntax keyword evergreenProof fact proof by ideal opaque affine partial axiom
syntax keyword evergreenTactic apply assumption cases constructor decide exact intro left right rfl simp_all omega
syntax keyword evergreenUnsafe trustme unsafe sorry
syntax keyword evergreenType bool nat integer isize usize i8 i16 i32 i64 i128 u8 u16 u32 u64 u128
syntax keyword evergreenType array plane linear_plane lone_plane never
syntax keyword evergreenRepresentation repr represents make_type align bits encoding endian signed size
syntax keyword evergreenBoolean true false null
syntax keyword evergreenBuiltin result old typeof shape pointees
syntax match evergreenNumber '\<\d\+\>'
syntax match evergreenOperator '[-+*/%<>=!&|]'
syntax match evergreenDelimiter '[(){}\[\],;.:]'
syntax match evergreenFunction '\<\h\w*\ze\s*('
syntax keyword evergreenTodo TODO FIXME XXX NOTE contained
syntax match evergreenComment '//.*$' contains=evergreenTodo,@Spell

highlight default link evergreenDeclaration Structure
highlight default link evergreenKeyword Keyword
highlight default link evergreenContract Keyword
highlight default link evergreenProof Keyword
highlight default link evergreenTactic Statement
highlight default link evergreenUnsafe WarningMsg
highlight default link evergreenType Type
highlight default link evergreenRepresentation Keyword
highlight default link evergreenBoolean Boolean
highlight default link evergreenBuiltin Special
highlight default link evergreenNumber Number
highlight default link evergreenOperator Operator
highlight default link evergreenDelimiter Delimiter
highlight default link evergreenFunction Function
highlight default link evergreenTodo Todo
highlight default link evergreenComment Comment

let b:current_syntax = 'evergreen'
