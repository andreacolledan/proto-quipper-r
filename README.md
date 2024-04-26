# Proto-Quipper-R
Proto-Quipper-R is a quantum circuit description language endowed with a linear-dependent type checker that can verify upper bounds on the width of the quantum circuits produced by a program. A more detailed description of a the language can be found [here](src/Lang/Unified/README.md).

## Getting started

Consider a function `dumbNot` defined as:
```
\q :: Qubit .
  let a = apply(QInit1,()) in       -- initialize a temporary qubit
  let (a,q) = apply(CNot,(a,q)) in  -- apply cnot between input and temporary qubit
  let _ = apply(QDiscard,a)         -- discard temporary qubit
  in q                              -- return input qubit
```
This function describes a very basic quantum computation in the form of a quantum circuit: the fundamental units of data are `Qubit`s and `Bit`s and computations on these data are carried out by applying elementary operations on them. These operations are either quantum gates (e.g. `CNot`, `Hadamard`, etc.) or other operations on bits and qubits (e.g.`QInit1`, `QDiscard`, `Measure`, etc.).

As the name suggests, `dumbNot` implements the negation of a qubit in a dumb, unnecessarily expensive way. But let's forget about the semantics of this function and let's focus instead on the circuit it builds. Applying `dumbNot` to an input qubit `q` produces the following circuit of width 2:

![](dumbnot-circuit.png)

Proto-Quipper-R is able to automatically derive this information from the definition of `dumbNot`, before it is even run, by inferring for it the following function type:
```
Qubit -o[2,0] Qubit
```
The linear arrow is indexed with two numbers: the first one tells us the width of the circuit build by `dumbNot` once applied to an argument (in this case, 2), while the second one tells us the number of wire references that are captured inside the function's closure (in this case, no wires are captured). The latter index, although exotic in nature, is essential to correctly estimate circuit width in many cases.

Proto-Quipper-R supports a limited form of depdendency, which is precisely restricted to the indices used to annotate types. This allows for the description of circuit families that depend on a natural number parameter. E.g. the `qft` circuit family is implemented as follows:
```
... -- definitions for rev, rotate, etc.

@i.\qs :: List[i] Qubit.
  let qftStep = lift @j.\(qs, q) :: (List[j] Qubit, Qubit). -- define the step function
    let revqs = ((force rev) @j) qs in
    let qqs = fold(rotate @j, (q, []), revqs) in
    let (q, qs) = qqs in
    let q = apply(Hadamard,q) in
    q:qs
  in fold(qftStep, [], qs)                                  -- fold it over the input list
```
Abstractions over index variables is achieved through the `@` binder. Indices are arithmetic expressions over natural numbers and index variables and are the only kind of term that's allowed to appear in types. Note also that general recursion is not available in Proto-Quipper-R. Instead, a limited form of recursion is made available via the primitive `fold` construct. Proto-Quipper-R infers the following type for `qft`:
```
i ->[0,0] List[i] Qubit -o[i,0] List[i] Qubit
```
meaning that for every `i`, `qft` takes as input `i` qubits and builds a circuit of width at most `i` that outputs a list of `i` qubits.

The whole code for `qft`, as well as other examples, can be found in the `examples` directory. 

## Installing
Note: Proto-Quipper-R requires [cvc5](https://cvc5.github.io) to be installed and present in your `PATH`.
You can then install Proto-Quipper-R by running

```
$ git clone https://github.com/andreacolledan/proto-quipper-r
$ cd proto-quipper-r
$ stack install
```

## Usage
To run the Proto-Quipper-R type checker on program file `FILE`, run
```
$ pqr FILE
```
Use option `--debug DEBUG` to dump a copy of all SMT queries performed during typechecking to file `DEBUG`. General usage is thus
```
pqr FILE [-v | --verbose] [-d | --debug DEBUG]
```
For more information, refer to `pqr --help`.

## Paper
This implementation is based on ["Colledan, A. and Lago, U.D. 2023. Circuit Width Estimation via Effect Typing and Linear Dependency (Long Version). arXiv."](https://doi.org/10.48550/arXiv.2310.19096)

## Tests
To execute unit tests, run `stack test`