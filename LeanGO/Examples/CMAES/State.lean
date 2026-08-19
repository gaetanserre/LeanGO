/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import LeanGO.Examples.ForMathlib.Multivariate

@[expose] public section

/-!
# The state and the strategy parameters of CMA-ES

## Main definitions

* `CMAES.State`: the state adapted by CMA-ES along the iterations.
* `CMAES.Params`: the strategy parameters, `CMAES.defaultParams` being the usual choice.

## References

* [(_The CMA Evolution Strategy: A Tutorial_, Hansen, 2023)](https://arxiv.org/abs/1604.00772)
-/

namespace CMAES

variable {d : ℕ}

/-- The state of CMA-ES: the mean `m`, the step size `σ`, the covariance matrix `C` and the
evolution paths `p_c` and `p_σ`. The associated sampling distribution is `𝓝(m, σ² C)`. -/
abbrev State (d : ℕ) := EuclideanSpace ℝ (Fin d) × ℝ × Matrix (Fin d) (Fin d) ℝ ×
  EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)

namespace State

/-- The mean `m`. -/
abbrev m (s : State d) : EuclideanSpace ℝ (Fin d) := s.1

/-- The step size `σ`. -/
abbrev σ (s : State d) : ℝ := s.2.1

/-- The covariance matrix `C`, up to the step size. -/
abbrev C (s : State d) : Matrix (Fin d) (Fin d) ℝ := s.2.2.1

/-- The evolution path `p_c`, driving the rank-one update of `C`. -/
abbrev p_c (s : State d) : EuclideanSpace ℝ (Fin d) := s.2.2.2.1

/-- The conjugate evolution path `p_σ`, driving the step size adaptation. -/
abbrev p_σ (s : State d) : EuclideanSpace ℝ (Fin d) := s.2.2.2.2

end State

/-- The strategy parameters of CMA-ES, i.e. the constants it does not adapt. -/
structure Params where
  /-- The recombination weights: `w i` is the weight of the point of rank `i`. They usually sum
  to one for `i < μ` and vanish for `i ≥ μ`, so that only the `μ` best points are recombined. -/
  w : ℕ → ℝ
  /-- The learning rate of `p_σ`. -/
  c_σ : ℝ
  /-- The damping of the step size update. -/
  d_σ : ℝ
  /-- The learning rate of `p_c`. -/
  c_c : ℝ
  /-- The learning rate of the rank-one update of `C`. -/
  c_1 : ℝ
  /-- The learning rate of the rank-`μ` update of `C`. -/
  c_μ : ℝ

/-- The variance effective selection mass `1 / ∑ w i ^ 2`. -/
noncomputable def Params.muEff (p : Params) (lam : ℕ) : ℝ :=
  (∑ i ∈ Finset.range lam, p.w i ^ 2)⁻¹

/-- The usual approximation `√d (1 - 1 / (4 d) + 1 / (21 d²))` of `𝔼‖𝓝(0, I_d)‖`. -/
noncomputable def chi (d : ℕ) : ℝ := √d * (1 - 1 / (4 * d) + 1 / (21 * d ^ 2))

/-- The default weights: `w i ∝ log ((λ + 1) / 2) - log (i + 1)` for the `⌊λ / 2⌋` best points,
normalized so that they sum to one, and `0` for the other ones. -/
noncomputable def defaultWeights (lam i : ℕ) : ℝ :=
  let w : ℕ → ℝ := fun j ↦ Real.log ((lam + 1) / 2) - Real.log (j + 1)
  if i < lam / 2 then w i / ∑ j ∈ Finset.range (lam / 2), w j else 0

/-- The default strategy parameters in dimension `d` for a generation of `λ` points, as suggested
in [(_The CMA Evolution Strategy: A Tutorial_, Hansen, 2023)](https://arxiv.org/abs/1604.00772).
-/
noncomputable def defaultParams (d lam : ℕ) : Params :=
  let w := defaultWeights lam
  let μ := (∑ i ∈ Finset.range lam, w i ^ 2)⁻¹
  let c_σ := (μ + 2) / (d + μ + 5)
  let c_1 := 2 / ((d + 1.3) ^ 2 + μ)
  { w := w
    c_σ := c_σ
    d_σ := 1 + 2 * max 0 (√((μ - 1) / (d + 1)) - 1) + c_σ
    c_c := (4 + μ / d) / (d + 4 + 2 * μ / d)
    c_1 := c_1
    c_μ := min (1 - c_1) (2 * (μ - 2 + 1 / μ) / ((d + 2) ^ 2 + μ)) }

end CMAES

end
