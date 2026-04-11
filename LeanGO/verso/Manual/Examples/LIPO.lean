/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanGO.Examples.LIPO
import VersoManual
import Manual.Papers

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

The LIPO algorithm has been introduced in {citep Malherbe2017}[] and is a more sophisticated stochastic iterative global optimization algorithm made for Lipschitz functions. It uses the Lipschitz constant to adaptively construct an upper bound that guides the sampling of the search space. More formally, at each iteration, LIPO samples uniformly from the set of _*potential maximizers*_ defined as
$$`
\left \{ x \in \alpha \; \middle| \; \max_{1 \le i \le n} f(X_i) \le \min_{1 \le i \le n} f(X_i) + \kappa \|X_i - x \|_2 \right\},
`
where {anchorTerm LIPOvars}`α` is a pseudo-metric, measurable, Borel, and second-countable space and $`\kappa` is the Lipschitz constant of the function $`f : \alpha \to \mathbb{R}`.

![](static/lipo_upper_bound.svg)

It can be represented in our framework as follows:

{docstring LIPO}

```anchor LIPO
noncomputable def LIPO : Algorithm α ℝ where
  ν := μ
  kernel_iter _ := potential_max_kernel μ κ
  markov_kernel n := ⟨fun data => cond_isProbabilityMeasure (h n data)⟩
```
