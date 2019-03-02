# itt

ITT supports the following modalities:
* **I** (irrelevance) -- erased at runtime, disregarded in conversion checks
* **E** (erased) -- erased at runtime, subject to conversion checks
* **L** (linear) -- present at runtime, linear
* **R** (unrestricted) -- present at runtime, unrestricted

ITT can infer all of them by interleaving type checking and constraint solving
using an external solver (Z3 via [SBV](http://hackage.haskell.org/package/sbv)).
With a bit of work (computing manually connected components of the equivalence graph),
we could remove the dependency on the external solver. That's future work for now.

ITT supports only variables, lambdas and applications so if you need global definitions,
you need to bring them into scope using lambdas. There's no pattern matching for now.

The inference algorithm does not need any modality annotations to work.
However, any "primitives" you bring into scope with lambdas have no bodies
so the minimal consistent annotation is "everything is irrelevant".
You'll probably want to override this to give more meaning to your primitives.

You can look at [one of the example programs](https://github.com/ziman/itt/blob/master/examples/irr-infer.tt)
and [the corresponding output](https://github.com/ziman/itt/blob/master/examples/irr-infer.out).

## Making it easier

Inference gets easier if you don't need to support all modalities.

* **I** requires interleaving conversion checking and constraint solving,
  iteratively, until you reach a fixed point where no new conversions arise.

* **L** requires counting constraints, which interferes with evar equalities.
  Namely, you can no longer express equality `p ~ q` as `(p -> q) /\ (q -> p)`.
  I use an external SMT solver to get it done.

If you leave out either of the two, you get an easier problem to solve
when inferring annotations.

## Usage

Either install `itt`:
```
$ git clone https://github.com/ziman/itt
$ cd itt
$ stack install
$ itt examples/irr-infer.tt
```

Or just use `stack exec`:
```
$ git clone https://github.com/ziman/itt
$ cd itt
$ stack build
$ stack exec itt examples/irr-infer.tt
```

For editing, https://github.com/ziman/ttstar-vim might come handy.
