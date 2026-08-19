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

set_option verso.exampleModule "LeanGO.Examples.CMAES.Basic"

#doc (Manual) "CMA-ES" =>
%%%
htmlSplit := .never
%%%

A general implementation of the CMA-ES algorithm in any dimension. As CMA-ES samples $`\lambda` points at each iteration, the input space of the algorithm is $`\mathbb{R}^{d \times \lambda}`, which represents a sequence of $`\lambda` points in $`\mathbb{R}^{d}`. The initial measure is the product of $`\lambda` standard multivariate Gaussian measures on $`\mathbb{R}^{d}`, and the kernel is defined as a product of $`\lambda` multivariate Gaussian measures, where the mean and covariance matrix are given by measurable functions of the past evaluations. These functions can be anything as long as they are measurable w.r.t. the history of the algorithm, thus allowing for any CMA-ES variant to be implemented in this framework.

{docstring CMA_ES}

```anchor CMA_ES
noncomputable def CMA_ES : Algorithm (ℝ_ d lam) β where
  ν := Measure.pi (fun _ ↦ multivariateGaussian m S)
  kernel_iter := CMAKernel d lam hmean hcovar
  markov_kernel n := ⟨fun a => by simp [CMAKernel]; infer_instance⟩
```

# The original CMA-ES

The historical instantiation of this scheme {citep Hansen1996}[] ranks the $`\lambda` points of each generation according to their evaluations and recombines the $`\mu` best ones. It adapts a state made of the mean $`m`, the step size $`\sigma`, the covariance matrix $`C` and two evolution paths $`p_c` and $`p_\sigma`, the points of a generation being sampled i.i.d. according to $`\mathcal{N}(m, \sigma^2 C)`.

## Ranking a generation

As `LeanGO` maximizes objective functions, a point of a generation is better than another one if its evaluation is greater, ties being broken by index:

```anchor better (module := LeanGO.Examples.CMAES.Rank)
def better (j k : Fin lam) : Prop := evals k < evals j ∨ (evals j = evals k ∧ j < k)
```

Rather than sorting the generation, which would require to manipulate a permutation of $`\{1, \dots, \lambda\}`, we count, for each point, the number of points that are better than it:

```anchor rank (module := LeanGO.Examples.CMAES.Rank)
noncomputable def rank (k : Fin lam) : ℕ := #{j | better evals j k}
```

{docstring CMAES.rank}

As `better` is a strict total order, this is a bijection between the points of the generation and $`\{0, \dots, \lambda - 1\}`: the rank of a point is its index in the sorted generation, the best point having rank $`0`.

## The state and the strategy parameters

{docstring CMAES.State}

{docstring CMAES.Params}

The strategy parameters are constants: only the state is adapted along the iterations. The usual values, which depend on the dimension and on the size of the generations, are given by:

{docstring CMAES.defaultParams}

## Updating the state

Writing $`x_{i:\lambda}` for the point of rank $`i`, $`y_{i:\lambda} = (x_{i:\lambda} - m) / \sigma` for its step and $`\langle y \rangle_w = \sum_{i = 1}^{\mu} w_i y_{i:\lambda}` for the weighted recombination of the steps, the state is updated as
$$`
\begin{aligned}
m' &= m + \sigma \langle y \rangle_w, \\
p_\sigma' &= (1 - c_\sigma) p_\sigma + \sqrt{c_\sigma (2 - c_\sigma) \mu_{\text{eff}}} \; C^{-\frac{1}{2}} \langle y \rangle_w, \\
\sigma' &= \sigma \exp\left(\frac{c_\sigma}{d_\sigma} \left(\frac{\|p_\sigma'\|}{\mathbb{E}\|\mathcal{N}(0, I)\|} - 1\right)\right), \\
p_c' &= (1 - c_c) p_c + h_\sigma \sqrt{c_c (2 - c_c) \mu_{\text{eff}}} \; \langle y \rangle_w, \\
C' &= \left(1 - c_1 - c_\mu \sum_i w_i\right) C + c_1 \left(p_c' {p_c'}^\top + (1 - h_\sigma) c_c (2 - c_c) C\right) + c_\mu \sum_{i = 1}^{\mu} w_i y_{i:\lambda} y_{i:\lambda}^\top.
\end{aligned}
`
The new mean is the weighted recombination of the $`\mu` best points, the step size is adapted along the conjugate evolution path $`p_\sigma` (the _cumulative step size adaptation_), and the covariance matrix is the sum of a rank-one update, driven by the evolution path $`p_c`, and of a rank-$`\mu` update, driven by the steps of the generation.

Since the weights vanish beyond the $`\mu`-th one, the sums over the sorted generation are simply sums over the generation, each point being weighted according to its rank:

```anchor weightedStep (module := LeanGO.Examples.CMAES.Update)
noncomputable def weightedStep : EuclideanSpace ℝ (Fin d) := ∑ k, p.w (rank evals k) • step s pop k
```

One iteration gathers the five rules above:

```anchor update (module := LeanGO.Examples.CMAES.Update)
noncomputable def update : State d :=
  (nextMean p s pop evals, nextStepSize p s pop evals, nextCov p g s pop evals,
    nextPathC p g s pop evals, nextPathσ p s pop evals)
```

{docstring CMAES.update}

## The algorithm

The state is a deterministic function of the past generations and of their evaluations, so that it can be recovered by recursion over the history of the algorithm:

```anchor state (module := LeanGO.Examples.CMAES.Original)
noncomputable def state : (n : ℕ) → prod_iter_image (ℝ_ d lam) (Fin lam → ℝ) n → State d
  | 0, data => update p 0 s₀ (data.1 ⟨0, mem_Iic.mpr le_rfl⟩) (data.2 ⟨0, mem_Iic.mpr le_rfl⟩)
  | n + 1, data => update p (n + 1)
      (state n (Tuple.subTuple n.le_succ data.1, Tuple.subTuple n.le_succ data.2))
      (data.1 ⟨n + 1, mem_Iic.mpr le_rfl⟩) (data.2 ⟨n + 1, mem_Iic.mpr le_rfl⟩)
```

{docstring CMAES.state}

The mean and the covariance matrix of the generation $`n + 1` being measurable functions of that state, the original CMA-ES is an instance of the above scheme, the evaluation space being $`\mathbb{R}^\lambda`:

```anchor CMA_ES_original (module := LeanGO.Examples.CMAES.Original)
noncomputable def CMA_ES_original (p : Params) (s₀ : State d) :
    Algorithm (ℝ_ d lam) (Fin lam → ℝ) :=
  CMA_ES d lam (measurable_mean p s₀) (measurable_covar p s₀) s₀.m (s₀.σ ^ 2 • s₀.C)
```

{docstring CMA_ES_original}
