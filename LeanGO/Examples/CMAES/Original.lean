/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import LeanGO.Examples.CMAES.Update

@[expose] public section

/-!
# The original CMA-ES

The state of CMA-ES is a deterministic function of the past generations and of their evaluations
(`CMAES.state`), so that the original algorithm is an instance of the general scheme `CMA_ES`,
the evaluation of a generation being the tuple of the values of the objective function at its
`λ` points.

## Main definitions

* `CMA_ES_original`: the original CMA-ES algorithm.

## References

* [(_The CMA Evolution Strategy: A Tutorial_, Hansen, 2023)](https://arxiv.org/abs/1604.00772)
-/

namespace CMAES

open Finset

variable {d lam : ℕ} (p : Params) (s₀ : State d)

/-- The state of CMA-ES once the generations `0, …, n` have been sampled and evaluated, starting
from `s₀`, i.e. the state from which the generation `n + 1` is sampled. -/
-- ANCHOR: state
noncomputable def state : (n : ℕ) → prod_iter_image (ℝ_ d lam) (Fin lam → ℝ) n → State d
  | 0, data => update p 0 s₀ (data.1 ⟨0, mem_Iic.mpr le_rfl⟩) (data.2 ⟨0, mem_Iic.mpr le_rfl⟩)
  | n + 1, data => update p (n + 1)
      (state n (Tuple.subTuple n.le_succ data.1, Tuple.subTuple n.le_succ data.2))
      (data.1 ⟨n + 1, mem_Iic.mpr le_rfl⟩) (data.2 ⟨n + 1, mem_Iic.mpr le_rfl⟩)
-- ANCHOR_END: state

lemma measurable_state : ∀ n, Measurable (state p s₀ (lam := lam) n) := by
  intro n
  induction n with
  | zero =>
    simp only [state]
    exact measurable_update p 0 measurable_const measurable_fst.eval measurable_snd.eval
  | succ n ih =>
    simp only [state]
    refine measurable_update p (n + 1) (ih.comp ?_) measurable_fst.eval measurable_snd.eval
    fun_prop

variable (n : ℕ) (data : prod_iter_image (ℝ_ d lam) (Fin lam → ℝ) n)

/-- The mean of the distribution from which the generation `n + 1` is sampled. -/
noncomputable def mean : EuclideanSpace ℝ (Fin d) := (state p s₀ n data).m

/-- The covariance matrix `σ² C` of the distribution from which the generation `n + 1` is
sampled. -/
noncomputable def covar : Matrix (Fin d) (Fin d) ℝ :=
  (state p s₀ n data).σ ^ 2 • (state p s₀ n data).C

lemma measurable_mean : ∀ n, Measurable (mean p s₀ (lam := lam) n) :=
  fun n ↦ (measurable_state p s₀ n).fst

lemma measurable_covar : ∀ n, Measurable (covar p s₀ (lam := lam) n) := by
  intro n
  have h := measurable_state p s₀ (lam := lam) n
  refine Matrix.measurable_iff.mpr fun i j ↦ ?_
  simp only [covar, Matrix.smul_apply, smul_eq_mul]
  fun_prop

end CMAES

section

open CMAES

variable {d lam : ℕ}

/-- The original CMA-ES algorithm for global optimization, starting from the state `s₀` and using
the strategy parameters `p`, e.g. `CMAES.defaultParams`. The `λ` points of each generation are
sampled i.i.d. according to `𝓝(m, σ² C)`, the state being updated by `CMAES.update`. It is meant
to be used with an evaluation function of the form `fun x i ↦ f (x i)`, `f` being the objective
function. -/
-- ANCHOR: CMA_ES_original
noncomputable def CMA_ES_original (p : Params) (s₀ : State d) :
    Algorithm (ℝ_ d lam) (Fin lam → ℝ) :=
  CMA_ES d lam (measurable_mean p s₀) (measurable_covar p s₀) s₀.m (s₀.σ ^ 2 • s₀.C)
-- ANCHOR_END: CMA_ES_original

end

end
