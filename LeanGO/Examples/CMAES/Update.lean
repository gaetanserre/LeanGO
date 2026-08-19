/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import LeanGO.Examples.CMAES.Basic
public import LeanGO.Examples.CMAES.Rank
public import LeanGO.Examples.CMAES.State

@[expose] public section

/-!
# The original update rules of CMA-ES

The update rules of [(_Completely Derandomized Self-Adaptation in Evolution Strategies_, Hansen
and Ostermeier, 2001)](https://doi.org/10.1162/106365601750190398), as described in
[(_The CMA Evolution Strategy: A Tutorial_, Hansen, 2023)](https://arxiv.org/abs/1604.00772):
the mean is the weighted recombination of the best points of the generation, the step size is
adapted by the conjugate evolution path `p_σ` and the covariance matrix by both a rank-one
update, driven by the evolution path `p_c`, and a rank-`μ` update, driven by the steps of the
generation.

Throughout, `pop` is the population of the current generation, i.e. its `λ` points, and `evals`
the evaluations of these points.

## Main definitions

* `CMAES.update`: one iteration of CMA-ES, updating the whole state.

## References

* [(_The CMA Evolution Strategy: A Tutorial_, Hansen, 2023)](https://arxiv.org/abs/1604.00772)
-/

namespace CMAES

open Finset Matrix Real

open scoped MatrixOrder Matrix.Norms.L2Operator

variable {d lam : ℕ} (p : Params) (g : ℕ) (s : State d) (pop : ℝ_ d lam) (evals : Fin lam → ℝ)

/-- The step `σ⁻¹ • (pop k - m)` of the `k`-th point of the generation. -/
noncomputable def step (k : Fin lam) : EuclideanSpace ℝ (Fin d) := s.σ⁻¹ • (pop k - s.m)

/-- The weighted recombination `∑ w i • y_{i:λ}` of the steps of the generation, `y_{i:λ}` being
the step of the point of rank `i`. -/
-- ANCHOR: weightedStep
noncomputable def weightedStep : EuclideanSpace ℝ (Fin d) := ∑ k, p.w (rank evals k) • step s pop k
-- ANCHOR_END: weightedStep

/-- The mean after one iteration. -/
noncomputable def nextMean : EuclideanSpace ℝ (Fin d) := s.m + s.σ • weightedStep p s pop evals

/-- The conjugate evolution path after one iteration. -/
noncomputable def nextPathσ : EuclideanSpace ℝ (Fin d) :=
  (1 - p.c_σ) • s.p_σ + √(p.c_σ * (2 - p.c_σ) * p.muEff lam) •
    toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt s.C)⁻¹ (weightedStep p s pop evals)

/-- The step size after one iteration, given by the cumulative step size adaptation. -/
noncomputable def nextStepSize : ℝ :=
  s.σ * exp (p.c_σ / p.d_σ * (‖nextPathσ p s pop evals‖ / chi d - 1))

/-- The Heaviside function stalling the update of `p_c` when `‖p_σ‖` is too large, `g` being the
index of the generation. -/
noncomputable def hσ : ℝ :=
  if ‖nextPathσ p s pop evals‖ / √(1 - (1 - p.c_σ) ^ (2 * (g + 1))) <
    (1.4 + 2 / (d + 1)) * chi d then 1 else 0

/-- The evolution path after one iteration. -/
noncomputable def nextPathC : EuclideanSpace ℝ (Fin d) :=
  (1 - p.c_c) • s.p_c +
    (hσ p g s pop evals * √(p.c_c * (2 - p.c_c) * p.muEff lam)) • weightedStep p s pop evals

/-- The covariance matrix after one iteration, i.e. the rank-one update `p_c p_cᵀ` plus the
rank-`μ` update `∑ w i • y_{i:λ} y_{i:λ}ᵀ`. -/
noncomputable def nextCov : Matrix (Fin d) (Fin d) ℝ :=
  (1 - p.c_1 - p.c_μ * ∑ k, p.w (rank evals k)) • s.C +
    p.c_1 • (vecMulVec (nextPathC p g s pop evals) (nextPathC p g s pop evals) +
      ((1 - hσ p g s pop evals) * p.c_c * (2 - p.c_c)) • s.C) +
    p.c_μ • ∑ k, p.w (rank evals k) • vecMulVec (step s pop k) (step s pop k)

/-- One iteration of CMA-ES, from the population of the generation `g` and its evaluations. -/
-- ANCHOR: update
noncomputable def update : State d :=
  (nextMean p s pop evals, nextStepSize p s pop evals, nextCov p g s pop evals,
    nextPathC p g s pop evals, nextPathσ p s pop evals)
-- ANCHOR_END: update

section Measurability

variable {α : Type*} [MeasurableSpace α] {s : α → State d} {pop : α → ℝ_ d lam}
  {evals : α → Fin lam → ℝ} (hs : Measurable s) (hpop : Measurable pop) (hevals : Measurable evals)

include hevals in
@[fun_prop]
lemma measurable_weight (k : Fin lam) : Measurable fun a ↦ p.w (rank (evals a) k) :=
  measurable_from_top.comp (measurable_rank hevals k)

include hs hpop in
@[fun_prop]
lemma measurable_step (k : Fin lam) : Measurable fun a ↦ step (s a) (pop a) k := by
  have hσ : Measurable fun a ↦ (s a).σ := hs.snd.fst
  have hm : Measurable fun a ↦ (s a).m := hs.fst
  have hpopk : Measurable fun a ↦ pop a k := hpop.eval
  simp only [step]
  fun_prop

include hs hpop hevals in
@[fun_prop]
lemma measurable_weightedStep : Measurable fun a ↦ weightedStep p (s a) (pop a) (evals a) := by
  simp only [weightedStep]
  refine Finset.measurable_sum _ fun k _ ↦ ?_
  have := measurable_weight p hevals k
  have := measurable_step hs hpop k
  fun_prop

include hs hpop hevals in
@[fun_prop]
lemma measurable_nextMean : Measurable fun a ↦ nextMean p (s a) (pop a) (evals a) := by
  have hσ : Measurable fun a ↦ (s a).σ := hs.snd.fst
  have hm : Measurable fun a ↦ (s a).m := hs.fst
  have := measurable_weightedStep p hs hpop hevals
  simp only [nextMean]
  fun_prop

include hs hpop hevals in
@[fun_prop]
lemma measurable_nextPathσ : Measurable fun a ↦ nextPathσ p (s a) (pop a) (evals a) := by
  have hp : Measurable fun a ↦ (s a).p_σ := hs.snd.snd.snd.snd
  have hC : Measurable fun a ↦ (s a).C := hs.snd.snd.fst
  have := measurable_weightedStep p hs hpop hevals
  have : Measurable fun a ↦ toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (s a).C)⁻¹
    (weightedStep p (s a) (pop a) (evals a)) := by fun_prop
  simp only [nextPathσ]
  fun_prop

include hs hpop hevals in
@[fun_prop]
lemma measurable_nextStepSize : Measurable fun a ↦ nextStepSize p (s a) (pop a) (evals a) := by
  have hσ : Measurable fun a ↦ (s a).σ := hs.snd.fst
  have := measurable_nextPathσ p hs hpop hevals
  simp only [nextStepSize]
  fun_prop

include hs hpop hevals in
@[fun_prop]
lemma measurable_hσ : Measurable fun a ↦ hσ p g (s a) (pop a) (evals a) := by
  have := (measurable_nextPathσ p hs hpop hevals).norm
  simp only [hσ]
  exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) measurable_const
    measurable_const

include hs hpop hevals in
@[fun_prop]
lemma measurable_nextPathC : Measurable fun a ↦ nextPathC p g (s a) (pop a) (evals a) := by
  have hp : Measurable fun a ↦ (s a).p_c := hs.snd.snd.snd.fst
  have := measurable_weightedStep p hs hpop hevals
  have := measurable_hσ p g hs hpop hevals
  simp only [nextPathC]
  fun_prop

include hs hpop hevals in
@[fun_prop]
lemma measurable_nextCov : Measurable fun a ↦ nextCov p g (s a) (pop a) (evals a) := by
  have hC : Measurable fun a ↦ (s a).C := hs.snd.snd.fst
  have := measurable_hσ p g hs hpop hevals
  have := measurable_nextPathC p g hs hpop hevals
  have : Measurable fun a ↦ ∑ k, p.w (rank (evals a) k) :=
    Finset.measurable_sum _ fun k _ ↦ measurable_weight p hevals k
  refine Matrix.measurable_iff.mpr fun i j ↦ ?_
  simp only [nextCov, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply,
    Matrix.sum_apply]
  have : Measurable fun a ↦ (s a).C i j := hC.eval_matrix
  have hpc : ∀ i, Measurable fun a ↦ nextPathC p g (s a) (pop a) (evals a) i := fun _ ↦ by fun_prop
  have : Measurable fun a ↦ ∑ k, p.w (rank (evals a) k) *
      (step (s a) (pop a) k i * step (s a) (pop a) k j) := by
    refine Finset.measurable_sum _ fun k _ ↦ ?_
    have := measurable_weight p hevals k
    have := measurable_step hs hpop k
    fun_prop
  have := hpc i
  have := hpc j
  fun_prop

include hs hpop hevals in
@[fun_prop]
lemma measurable_update : Measurable fun a ↦ update p g (s a) (pop a) (evals a) := by
  simp only [update]
  exact (measurable_nextMean p hs hpop hevals).prodMk <|
    (measurable_nextStepSize p hs hpop hevals).prodMk <|
      (measurable_nextCov p g hs hpop hevals).prodMk <|
        (measurable_nextPathC p g hs hpop hevals).prodMk (measurable_nextPathσ p hs hpop hevals)

end Measurability

end CMAES

end
