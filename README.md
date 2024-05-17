# Verified linked list

Author: [Clément CHAPOT](clement@chapot.ovh) <br>
Description: Linked list verified using Verus

## Project description

- the `View` (abstract representation) of a `LinkedList` is a `Seq`
- `linked_list_iter.rs` provides an example of how to implement an iterator using Verus
- `src/main.rs` contains an example of what can be verified using Verus on the linked list and its iterator
- we only use two `assume` statements (axioms) to tell Verus what is the correspondance between a `Node` and its `View`

## Verify

Verify the crate using Verus:

```bash
verus src/main.rs
```

## Run

Run `main.rs` using cargo:

```bash
cargo run
```
