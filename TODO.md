# TODO

## Design

### Circuits

 - [x] Decide how to represent circuits, circuits with input and circuit-building computations
 - [ ] Decide how programs are meant to be executed: from a starting circuit or standalone. Consequently, choose whether $Q$ should appear in the implementation of the language type system or not.

## Implementation

### Wire language

- [x] Implement pairs of labels
- [ ] Implement sized lists of labels

### Language

- [ ] Implement remaining language constructs
  - [x] Tuples and destructuring let
  - [ ] Functions
  - [ ] Lifting and forcing (boxing and unboxing linear values)
  - [ ] Lists and fold

### Typechecking

- [ ] Interface with SMT solvers
- [ ] Better error messages
