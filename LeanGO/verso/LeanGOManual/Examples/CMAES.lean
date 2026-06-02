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


We provide an implementation of the CMA-ES (Covariance Matrix Adaptation - Evolution Strategy) algorithm {citep Hansen1996}[] whenever the search space is one-dimensional, as the multivariate Gaussian distribution is not yet implemented in Mathlib. The implementation is general in the sense that the mean and variance of the Gaussian kernel at each iteration are given by measurable functions of the past evaluations, thus allowing for any CMA-ES variant to be implemented in this framework. The initial measure is the product of $`\lambda` Gaussian measures with mean $`m` and variance $`v`, and the kernel is defined as a product of $`\lambda` Gaussian measures, where the mean and variance are given by measurable functions of the past evaluations.

{docstring CMA_ES}

```anchor CMA_ES
noncomputable def CMA_ES : Algorithm (ℝ_ lam) (ℝ_ lam) where
  ν := Measure.pi (fun _ ↦ gaussianReal m v)
  kernel_iter := CMAKernel lam hmean hvar
  markov_kernel n := ⟨fun a => by simp [CMAKernel]; infer_instance⟩
```
