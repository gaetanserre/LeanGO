# LeanGO

LeanGO is a Lean 4 library dedicated to the formalization of global optimization algorithms and is associated the the paper [_A Unifying Framework for Global Optimization: From Theory to Formalization_](https://arxiv.org/abs/2508.20671).

## Documentation

For more details on the theoretical background, specifically the consistency of stochastic iterative algorithms, please refer to the [documentation](https://gaetanserre.fr/LeanGO).

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

Some examples of how to use LeanGO can be found in the [Examples](LeanGO/Examples/) directory. In particular, the file [PRS.lean](LeanGO/Examples/PRS.lean) contains the formalization of the Pure Random Search algorithm, which is the simplest global optimization algorithm.

To see a more complex example of how to use LeanGO, check out [LipoCons](https://github.com/gaetanserre/LipoCons) : the formalization of the equivalence between consistency and convergence in probability for Lipschitz functions.
