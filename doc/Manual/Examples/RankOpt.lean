/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import VersoManual
import Manual.Papers

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option pp.rawOnError true

set_option verso.exampleProject "../"

set_option verso.exampleModule "LeanGO.Examples.RankOpt"

#doc (Manual) "RankOpt" =>
%%%
htmlSplit := .never
%%%

The RankOpt algorithm has been introduced in {citep Malherbe2016}[] and is a complex stochastic iterative global optimization algorithm. It is based on the notion of a _ranking rule_, which is a function induced by another function $`f` and is defined as
$$`
r_f (x, y) = \begin{cases}
1 & \text{if } f(x) > f(y) \\
0 & \text{if } f(x) = f(y) \\
-1 & \text{if } f(x) < f(y)
\end{cases}.
`
Ranking rules define equivalence classes of functions that share the same induced ranking. To use RankOpt, one needs to define a countable set of ranking rules $`\mathcal{R}` (e.g. a subset of the ranking rules induced by continuous functions). The algorithm samples points $`x` such that, for any ranking rule $`r \in \mathcal{R}` that is consistent with the observed data, $`0 \le r(x, \arg \max_{1 \le i \le n} f(X_i))`. The set of such points is the set of _potential maximizers_ of the algorithm and is defined as
$$`
\left \{x \in \alpha \; \middle| \; \exists r \in \mathcal{R}, \; \mathcal{L}_n(r) = 0 \land 0 \le r(x, \arg \max_{1 \le i \le n} f(X_i))\right\},
`
where $`\alpha` is a measurable subset of $`\mathbb{R}^d` with finite and non-zero measure and $`\mathcal{L}_n(r)` is the ranking loss of $`r` on the observed data, defined as
$$`
\mathcal{L}_n(r) \triangleq \frac{2}{n (n + 1)} \sum_{1 \le i \le j \le n} \mathbb{I}\left[r(X_i, X_j) \neq r_f(X_i, X_j)\right].
`
Note that RankOpt does not require to know $`r_f` explicitly as it is evaluated only on observed data points.

RankOpt can be represented in our framework as follows:

```anchor RankOptvars
variable {α : Type} [MeasurableSpace α] {d : ℕ} {α : Set (ℝᵈ d)}
  (mes_α : MeasurableSet α) (mα₀ : ℙ α ≠ 0) (mα₁ : ℙ α ≠ ⊤)
  {𝓡 : Set (RankRule α)} (h𝓡 : 𝓡.Countable)
```

```anchor RankOpt
noncomputable def RankOpt : Algorithm α ℝ where
  ν := uniform Set.univ
  prob_measure := by
    have := i₁ mes_α mα₁
    refine uniform_is_prob_measure ?_
    rwa [Measure.Subtype.volume_univ mes_α.nullMeasurableSet]
  kernel_iter _ := potential_max_kernel mes_α mα₁ h𝓡
  markov_kernel n := by
    refine ⟨fun data ↦ ?_⟩
    have := i₁ mes_α mα₁
    refine uniform_is_prob_measure <| h n data
```

where {anchorTerm RankRule}`RankRule` is defined as the subtype of $`\{-1, 0, 1\}`-valued functions that are jointly measurable:

```anchor RankRule
def RankRule (α : Type) [MeasurableSpace α] :=
  {f : α → α → ({-1, 0, 1} : Set ℝ) // Measurable <| Function.uncurry f}
```
