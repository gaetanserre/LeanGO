/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanGO.Examples.LIPO
import VersoManual
import LeanGOManual.Papers

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option pp.rawOnError true

set_option verso.exampleProject "."

set_option verso.exampleModule "LeanGO.Examples.LIPO"

#doc (Manual) "LIPO" =>
%%%
htmlSplit := .never
%%%

The LIPO algorithm has been introduced in {citep Malherbe2017}[] and is a decision-based global optimization algorithm made for Lipschitz functions. It uses the Lipschitz constant to adaptively construct an upper bound that guides the sampling of the search space. More formally, at each iteration, LIPO samples from the set of _*potential maximizers*_ defined as
$$`
\left \{ x \in \alpha \; \middle| \; \max_{1 \le i \le n} f(X_i) \le \min_{1 \le i \le n} f(X_i) + \kappa \|X_i - x \|_2 \right\},
`
where `α` is a pseudo-metric, measurable, Borel, and second-countable space and $`\kappa` is the Lipschitz constant of the function $`f : \alpha \to \mathbb{R}`.

![](static/lipo_upper_bound.svg)

It can be represented in our framework as a special case of the `Decision` structure, where the decision rules return $`1` if the candidate solution is in the set of potential maximizers and $`0` otherwise:

```anchor LIPO
noncomputable def LIPO : Algorithm α ℝ :=
  Decision μ (fun _ ↦ measurableSet_potential_max_prod κ) h
```

Note that LIPO requires the set of potential maximizers to have non-zero measure at each iteration, ensuring that the algorithm can sample from it. This is a non-trivial assumption that depends on the choice of the initial probability measure `μ`, the function to optimize, and the $`\sigma`-algebra on the search space.

{docstring LIPO}
