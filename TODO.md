# TODO

## Design

### Circuits

 - [x] Decide how to represent circuits, circuits with input and circuit-building computations. (Done: as in the paper)
 - [x] Decide how programs are meant to be executed: from a starting circuit or standalone. Consequently, choose whether $Q$ should appear in the implementation of the language type system or not. (Done: the former)

### Subtyping
 - [ ] Decide whether to inline subtyping (easier) or have bespoke subtyping rules (closer to the paper).

## Implementation

### Wire language checking

- [x] Label pairs
  - [x] Implementing
  - [x] Testing
- [ ] Implement sized lists of labels
  - [ ] Implementing
  - [ ] Testing

### PQR Language checking

- [ ] Language constructs
  - [x] Boxed circuits and apply
    - [x] Implementing boxed circuits
    - [x] Testing boxed circuits
    - [x] Implementing apply
    - [x] Testing apply
  - [x] Tuples and destructuring let
    - [x] Implementing tuples
    - [x] Testing tuples
    - [x] Implementing destructuring let
    - [x] Testing destructuring let
  - [x] Abstraction and application
    - [x] Implementing abstraction
    - [x] Testing abstraction
    - [x] Implementing application
    - [x] Testing application
  - [x] Lifting and forcing (aka linear boxing and unboxing of terms)
    - [x] Implementing lift
    - [x] Testing lift
    - [x] Implementing force
    - [x] Testing force
  - [x] Return and sequencing let
    - [x] Implementing return
    - [x] Testing return
    - [x] Implementing sequencing let
    - [x] Testing sequencing let
  - [x] Circuit boxing
    - [x] Implementing box
    - [x] Testing box
  - [ ] Lists and fold
    - [ ] Implementing lists
    - [ ] Testing lists
    - [ ] Implementing fold
    - [ ] Testing fold
- [ ] Subsumption (e.g. `⊢ m : Circ 1 (Qubit,Qubit) ; 5` entails `⊢ m : Circ 2 (Qubit,Qubit) ; 8`)
  - [ ] Decide whether to implement subsumption as a distinct case or within rules
  - [ ] Implement subsumption
    - [ ] Implement subtyping
      - [ ] Interface with SMT solver
- [ ] Instantiation (e.g. `⊢ f : List i Qubit -o [i,0] List i Qubit` entails `⊢ f : List 3 Qubit -o [3,0] List 3 Qubit`)
  - [ ] Implement instantiation

## PQR Language Type Synthesis

  - [ ] Type synthesis for lists
  - [ ] Type synthesis for fold
  - [ ] Testing synthesis

- [x] Better error messages
