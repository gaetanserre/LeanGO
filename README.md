# LeanGO

LeanGO is a Lean 4 library dedicated to the formalization of global optimization algorithms.

## Documentation

For more details on the theoretical background, specifically the consistency of stochastic iterative algorithms, please refer to the documentation:

[LipoCons — Stochastic iterative algorithm](https://gaetanserre.fr/LipoCons/Stochastic-iterative-algorithm/#Consistency-of-global-optimization-algorithms--Stochastic-iterative-algorithm)

## Installation

To use LeanGO in your Lean 4 project, add the following dependency to your `lakefile.lean`:

```lean
require LeanGO from git "https://github.com/gaetanserre/LeanGO" @ "main"
```

or to your lakefile.toml:

```toml
[[require]]
name = "leango"
git = "https://github.com/gaetanserre/LeanGO"
```

Then, run `lake update` to fetch the package (or `lake update leango` if your project has already fetched other dependencies).

## Example of use

To see a complex example of how to use LeanGO, check out [LipoCons](https://github.com/gaetanserre/LipoCons) : the formalization of the equivalence between consistency and convergence in probability for Lipschitz functions.
