# Proto-Quipper-R
Proto-Quipper-R is a typechecker for Proto-Quipper that can check upper bounds on the width of the quantum circuits produced by a program.

As an example, consider a function `dumbNot` defined as:
```
\q :: Qubit .
  let a = apply(QInit1,()) in
  let (a,q) = apply(CNot,(a,q)) in
  let _ = apply(QDiscard,a) in q
```
applying `dumbNot` on an input `q` produces the following circuit of width 2:

![](example-circuit.png)

Running the Proto-Quipper-R typechecker on `dumbNot` returns the following type:
```
Qubit ->[2,0] Qubit
```
which correctly reflects the idea that `dumbNot` takes as input a qubit and produces a circuit of width 2 (the first annotation on the arrow) which outputs a qubit.
The second annotation on the arrow tells us that this function does not capture any wires from the surrounding environment.

More examples programs can be found in the `examples/unified` folder.


## Installing
Note: Proto-Quipper-R requires [cvc5](https://cvc5.github.io) to be installed and present in your `PATH`.
You can then install Proto-Quipper-R by running

```
$ git clone https://github.com/andcol/proto-quipper-r
$ cd proto-quipper-r
$ stack install
```

## Usage

```
$ pqr filepath [-v] [-h] [-p] [--version]
```
Flag `-p` instructs the type-checker to accept the original syntax from [the paper](https://doi.org/10.48550/arXiv.2310.19096). This is useful for demonstration purposes, but it is otherwise a less usable syntax: terms and values are syntactically distinct, and as such terms must be evaluated explicitly as the left-hand side of a let-in before their result can be used to build bigger terms.
Furthermore, there is no explicit quantification over index variables.

## Paper
This implementation is based on ["Colledan, A. and Lago, U.D. 2023. Circuit Width Estimation via Effect Typing and Linear Dependency (Long Version). arXiv."](https://doi.org/10.48550/arXiv.2310.19096)

## Tests
To execute unit tests, run `stack test`