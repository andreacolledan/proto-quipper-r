## Language Documentation (WIP)

As a language, Proto-Quipper-R is based on the Proto-Quipper family of theoretical programming languages. As such, Proto-Quipper-R is, at its core, a lambda calculus with bespoke constructs to describe and manipulate quantum circuits.

## Basics

### Bits, Qubits and Circuits
The fundamental objects of circuit-building are `Bit`s and `Qubit`s. Because Proto-Quipper-R is a *circuit description language*, values of these types do not store the state of a bit or qubit. Rather, they are references to available wires in a global underlying circuit that is built incrementally as the program executes. You can think of them as the quantum circuit counterpart to pointers to memory locations.

Unlike memory locations, however, bits and qubits have to obey additional constraints: due to the no-cloning property of quantum states, thet cannot be duplicated, and due to decoherence they cannot go out of scope either. Whenever a new bit or qubit is initialized, it must be used *exactly once*, that is to say, bit and qubit references obey a linear typing discipline.

All operations that have an impact on the circuit being built must be carried out through the `apply` operator. This inlcude bit and qubit initialization. `apply` takes as arguments a circuit operation `op` and a collection of wire references `wr` to be fed to that operation (or `()` if `op` takes no input). It then emits said operation to the underlying circuit and returns a new collection of wires, corresponding to the outputs of `op`.

For example, we can initialize a qubit, apply some gates to it and discard it as follows:
```
let q = apply(QInit0, ()) in
let q = apply(Hadamard, q) in
apply(QDiscard, q)
```
where `QInit0`, `Hadamard` and `QDiscard` are primitive circuit operations in Proto-Quipper-R. You can find a list of all primitive circuit operations can be found at the end of this document.

### Dependent Linear Functions
TODO linear functions, index quantification

### Custom Circuit Operations
TODO box

### Recursion
TODO fold

## Type Checking and Width Verification

TODO

## Primitive Operations

At the time of writing, the following are the primitive operations that can be used for circuit-building in Proto-Quipper-R

### Qubit and Bit meta-operations

- `QInit0` and `QInit1` initialize a new `Qubit` to the states $|0\rangle$ and $|1\rangle$, respectively.
- `QDiscard` discards a `Qubit`.
- `CInit0` and `CInit1` initialize a new `Bit` to the states $0$ and $1$, respectively.
- `CDiscard` discards a `Bit`.
- `Meas` measures a `Qubit`, returning a `Bit`.
  
### Single-qubit gates

- `Hadamard` performs the Hadamard transform on a single `Qubit`.
- `PauliX` flips a single `Qubit` over the x-axis, i.e. it negates its input.
- `PauliY` flips a single `Qubit` over the y-axis.
- `PauliZ` flips a single `Qubit` over the z-axis.

### Multi-qubit gates

- `CNot` takes as input a pair of `Qubit`s and negates the second (the *target*) if the first (the *control*) is $|1\rangle$. The control qubit is returned unchanged.
- `Toffoli` takes as input three `Qubit`s and negates the third (the *target*) if the first two (the *controls*) are $|1\rangle$. The control qubits are returned unchanged.
- `MakeCRGate @i`, where `i` is a natural number, takes as input a pair of `Qubit`s and shifts the phase of the second (the *target*) by $2π/2^i$ radians if the first (the *control*) is $|1\rangle$. The control qubit is returned unchanged.