/-
 - Created in 2025 by Gaëtan Serré
-/

import VersoManual
import Manual.Papers

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option pp.rawOnError true

set_option verso.exampleProject "../"

set_option verso.exampleModule "LeanGO.Examples.LIPO"

#doc (Manual) "LIPO" =>
%%%
htmlSplit := .never
%%%

The LIPO algorithm has been introduced in {citep Malherbe2017}[] and is a more sophisticated stochastic iterative global optimization algorithm made for Lipschitz functions. It uses the Lipschitz constant to adaptively construct an upper bound that guides the sampling of the search space. More formally, at each iteration, LIPO samples uniformly from the set of _*potential maximizers*_ defined as
$$`
\left \{ x \in \alpha \; \middle| \; \max_{1 \le i \le n} f(X_i) \le \min_{1 \le i \le n} f(X_i) + \kappa \|X_i - x \|_2 \right\},
`
where $`\alpha` is a measurable subset of $`\mathbb{R}^d` with finite and non-zero measure and $`\kappa` is the Lipschitz constant of the function $`f : \alpha \to \mathbb{R}`.

![](static/lipo_upper_bound.svg)

It can be represented in our framework as follows:

```anchor LIPOvars
variable {d : ℕ} {κ : ℝ≥0} {α : Set (ℝᵈ d)} (mes_α : MeasurableSet α)
  (mα₀ : ℙ α ≠ 0) (mα₁ : ℙ α ≠ ⊤)
```

```anchor LIPO
noncomputable def LIPO : Algorithm α ℝ where
  ν := uniform Set.univ
  prob_measure := by
    have := i₁ mes_α mα₁
    refine uniform_is_prob_measure ?_
    rwa [Measure.Subtype.volume_univ mes_α.nullMeasurableSet]
  kernel_iter _ := potential_max_kernel mes_α mα₁ κ
  markov_kernel n := by
    refine ⟨fun data => ?_⟩
    have := i₁ mes_α mα₁
    exact uniform_is_prob_measure <| h n data
```
