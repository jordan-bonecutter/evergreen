//! Persistent compressed binary trie. Keys are exact integer identities; there
//! is no hashing or collision policy. Branches test successively lower bits.

use std::sync::Arc;

type Link<V> = Arc<Node<V>>;

#[derive(Debug)]
enum Node<V> {
    Leaf {
        key: u128,
        value: V,
    },
    Branch {
        prefix: u128,
        mask: u128,
        left: Link<V>,
        right: Link<V>,
    },
}

#[derive(Debug)]
pub(super) struct Map<V> {
    root: Option<Link<V>>,
    len: usize,
}

impl<V> Default for Map<V> {
    fn default() -> Self {
        Self { root: None, len: 0 }
    }
}
impl<V> Clone for Map<V> {
    fn clone(&self) -> Self {
        Self {
            root: self.root.clone(),
            len: self.len,
        }
    }
}

fn prefix(key: u128, mask: u128) -> u128 {
    key & !(mask | (mask - 1))
}
fn highest_bit(value: u128) -> u128 {
    1 << (u128::BITS - 1 - value.leading_zeros())
}

fn branch<V>(key: u128, mask: u128, new: Link<V>, old: Link<V>) -> Link<V> {
    let (left, right) = if key & mask == 0 {
        (new, old)
    } else {
        (old, new)
    };
    Arc::new(Node::Branch {
        prefix: prefix(key, mask),
        mask,
        left,
        right,
    })
}

fn insert<V>(node: &Link<V>, key: u128, leaf: Link<V>) -> (Link<V>, bool) {
    match node.as_ref() {
        Node::Leaf { key: old, .. } if *old == key => (leaf, false),
        Node::Leaf { key: old, .. } => (
            branch(key, highest_bit(key ^ old), leaf, node.clone()),
            true,
        ),
        Node::Branch {
            prefix: common,
            mask,
            ..
        } if prefix(key, *mask) != *common => (
            branch(key, highest_bit(key ^ common), leaf, node.clone()),
            true,
        ),
        Node::Branch {
            prefix,
            mask,
            left,
            right,
        } => {
            let (left, right, added) = if key & mask == 0 {
                let (next, added) = insert(left, key, leaf);
                (next, right.clone(), added)
            } else {
                let (next, added) = insert(right, key, leaf);
                (left.clone(), next, added)
            };
            (
                Arc::new(Node::Branch {
                    prefix: *prefix,
                    mask: *mask,
                    left,
                    right,
                }),
                added,
            )
        }
    }
}

fn collect<V>(node: &Link<V>, out: &mut std::collections::BTreeSet<u128>) {
    match node.as_ref() {
        Node::Leaf { key, .. } => {
            out.insert(*key);
        }
        Node::Branch { left, right, .. } => {
            collect(left, out);
            collect(right, out);
        }
    }
}

fn header<V>(node: &Node<V>) -> (u128, u128) {
    match node {
        Node::Leaf { key, .. } => (*key, 0),
        Node::Branch { prefix, mask, .. } => (*prefix, *mask),
    }
}

fn changes<V>(
    a: &Link<V>,
    b: &Link<V>,
    out: &mut std::collections::BTreeSet<u128>,
    work: &mut usize,
) {
    *work += 1;
    if Arc::ptr_eq(a, b) {
        return;
    }
    let (ak, am) = header(a);
    let (bk, bm) = header(b);
    match (a.as_ref(), b.as_ref()) {
        (
            Node::Branch {
                left: al,
                right: ar,
                ..
            },
            Node::Branch {
                left: bl,
                right: br,
                ..
            },
        ) if am == bm && ak == bk => {
            changes(al, bl, out, work);
            changes(ar, br, out, work);
        }
        (Node::Branch { left, right, .. }, _) if am > bm && prefix(bk, am) == ak => {
            if bk & am == 0 {
                changes(left, b, out, work);
                collect(right, out);
            } else {
                collect(left, out);
                changes(right, b, out, work);
            }
        }
        (_, Node::Branch { left, right, .. }) if bm > am && prefix(ak, bm) == bk => {
            if ak & bm == 0 {
                changes(a, left, out, work);
                collect(right, out);
            } else {
                collect(left, out);
                changes(a, right, out, work);
            }
        }
        _ => {
            collect(a, out);
            collect(b, out);
        }
    }
}

impl<V> Map<V> {
    pub(super) fn get(&self, key: u128) -> Option<&V> {
        let mut node = self.root.as_deref()?;
        loop {
            node = match node {
                Node::Leaf { key: old, value } => return (*old == key).then_some(value),
                Node::Branch {
                    prefix: common,
                    mask,
                    left,
                    right,
                } => {
                    if prefix(key, *mask) != *common {
                        return None;
                    }
                    if key & mask == 0 {
                        left.as_ref()
                    } else {
                        right.as_ref()
                    }
                }
            };
        }
    }

    pub(super) fn insert(&self, key: u128, value: V) -> Self {
        let leaf = Arc::new(Node::Leaf { key, value });
        let (root, added) = match &self.root {
            Some(root) => insert(root, key, leaf),
            None => (leaf, true),
        };
        Self {
            root: Some(root),
            len: self.len + usize::from(added),
        }
    }

    pub(super) fn changed_keys(&self, other: &Self) -> std::collections::BTreeSet<u128> {
        let mut out = std::collections::BTreeSet::new();
        match (&self.root, &other.root) {
            (Some(a), Some(b)) => changes(a, b, &mut out, &mut 0),
            (Some(node), None) | (None, Some(node)) => collect(node, &mut out),
            _ => {}
        }
        out
    }

    pub(super) fn iter(&self) -> Iter<'_, V> {
        Iter {
            pending: self.root.as_deref().into_iter().collect(),
        }
    }
}

pub(super) struct Iter<'a, V> {
    pending: Vec<&'a Node<V>>,
}
impl<'a, V> Iterator for Iter<'a, V> {
    type Item = (u128, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.pending.pop() {
            match node {
                Node::Leaf { key, value } => return Some((*key, value)),
                Node::Branch { left, right, .. } => {
                    self.pending.push(right);
                    self.pending.push(left);
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    #[test]
    fn updates_match_ordered_map_and_preserve_old_roots() {
        let mut persistent = Map::default();
        let mut reference = BTreeMap::new();
        let mut snapshots = Vec::new();
        let mut random = 17u128;
        for value in 0..2048 {
            random = random
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let key = if value % 2 == 0 { random } else { random & 255 };
            if value % 97 == 0 {
                snapshots.push((persistent.clone(), reference.clone()));
            }
            persistent = persistent.insert(key, value);
            reference.insert(key, value);
            assert_eq!(persistent.get(key), reference.get(&key));
            assert_eq!(persistent.len, reference.len());
        }
        snapshots.push((persistent, reference));
        for pair in snapshots.windows(2) {
            let ((a, av), (b, bv)) = (&pair[0], &pair[1]);
            let expected = av
                .keys()
                .chain(bv.keys())
                .filter(|key| av.get(key) != bv.get(key))
                .copied()
                .collect();
            assert_eq!(a.changed_keys(b), expected);
        }
        for (old, expected) in snapshots {
            assert_eq!(
                old.iter().map(|(k, v)| (k, *v)).collect::<BTreeMap<_, _>>(),
                expected
            );
            for (key, value) in expected {
                assert_eq!(old.get(key), Some(&value));
            }
        }
    }

    #[test]
    fn one_update_skips_shared_subtrees() {
        let mut base = Map::default();
        for key in 0..4096 {
            base = base.insert(key, key);
        }
        let next = base.insert(1234, 99);
        let mut keys = std::collections::BTreeSet::new();
        let mut work = 0;
        changes(
            base.root.as_ref().unwrap(),
            next.root.as_ref().unwrap(),
            &mut keys,
            &mut work,
        );
        assert_eq!(keys, std::collections::BTreeSet::from([1234]));
        assert!(work < 100, "visited {work} nodes for one changed entry");
        let extended = next.insert(1 << 100, 7);
        assert_eq!(
            base.changed_keys(&extended),
            std::collections::BTreeSet::from([1234, 1 << 100])
        );
    }

    #[test]
    fn boundary_bits_and_forks_have_independent_values() {
        let keys = [0, 1, 2, 1 << 63, 1 << 64, 1 << 127, u128::MAX];
        for ordering in [keys, {
            let mut reversed = keys;
            reversed.reverse();
            reversed
        }] {
            let mut base = Map::default();
            for key in ordering {
                base = base.insert(key, key);
            }
            let left = base.insert(0, 42);
            let right = base.insert(u128::MAX, 7);
            assert_eq!(base.get(0), Some(&0));
            assert_eq!(left.get(0), Some(&42));
            assert_eq!(right.get(0), Some(&0));
            assert_eq!(left.get(u128::MAX), Some(&u128::MAX));
            assert_eq!(right.get(u128::MAX), Some(&7));
            assert_eq!(base.iter().map(|(key, _)| key).collect::<Vec<_>>(), keys);
            assert_eq!(base.get(3), None);
        }
    }
}
