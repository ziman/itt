# itt

ITT infers irrelevance *and* erasure by interleaving constraint solving and type checking.

ITT supports only variables, lambdas and applications so if you need global definitions,
you need to bring them into scope using lambdas. There's no pattern matching for now.

You can look at [one of the example programs](https://github.com/ziman/itt/blob/master/examples/irr-infer.tt).

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
