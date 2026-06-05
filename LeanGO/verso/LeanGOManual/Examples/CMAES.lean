/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanGOManual.Papers
import LeanGO.Examples.CMAES
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option pp.rawOnError true

set_option verso.exampleProject "."

set_option verso.exampleModule "LeanGO.Examples.CMAES"

#doc (Manual) "CMA-ES" =>
%%%
htmlSplit := .never
%%%

A general implementation of the CMA-ES algorithm in any dimension. As CMA-ES samples $`\lambda` points at each iteration, the input space of the algorithm is $`\mathbb{R}^{d \times \lambda}`, which represents a sequence of $`\lambda` points in $`\mathbb{R}^{d}`. The initial measure is the product of $`\lambda` standard multivariate Gaussian measures on $`\mathbb{R}^{d}`, and the kernel is defined as a product of $`\lambda` multivariate Gaussian measures, where the mean and variance are given by measurable functions of the past evaluations. These functions can be anything as long as they are measurable w.r.t. the history of the algorithm, thus allowing for any CMA-ES variant to be implemented in this framework.

{docstring CMA_ES}

```anchor CMA_ES
noncomputable def CMA_ES : Algorithm (ℝ_ d lam) (ℝ_ d lam) where
  ν := Measure.pi (fun _ ↦ multivariateGaussian m v)
  kernel_iter := CMAKernel d lam hmean hvar
  markov_kernel n := ⟨fun a => by simp [CMAKernel]; infer_instance⟩
```
