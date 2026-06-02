/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanGO.Algorithm
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

open MeasureTheory ProbabilityTheory NNReal

/-!
# CMA-ES: Covariance Matrix Adaptation - Evolution Strategy

A simple yet general implementation of the CMA-ES algorithm in one dimension. As CMA-ES
samples `λ` points at each iteration, the input space of the algorithm is `ℝ^λ`, which
represents a sequence of `λ` real numbers. The initial measure is the product of `λ` standard Gaussian measures on `ℝ^λ`, and the kernel is defined as a product of `λ` Gaussian measures, where the mean and variance are given by measurable functions of the past evaluations. These functions
can be anything as long as they are measurable w.r.t. the history of the algorithm, thus allowing for any CMA-ES variant to be implemented in this framework.
-/

section Equiv

variable (n : ℕ)

noncomputable
def EuclideanSpace.mequiv_fin : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵐ (Fin (n + 1) → ℝ) := by
  have := EuclideanSpace.equiv (Fin (n + 1)) ℝ
  refine ⟨this, this.continuous_toFun.measurable, this.continuous_invFun.measurable⟩

noncomputable
def iter_mequiv_euclidean : iter ℝ n ≃ᵐ EuclideanSpace ℝ (Fin (n + 1)) :=
  (iter_mequiv _ _).trans <| (EuclideanSpace.mequiv_fin n).symm

/- One could define R_lam := EuclideanSpace ℝ <| Fin (lam + 1) and pushforward the Gaussian
measure through the measurable equivalence, allowing the definition of the kernel using
`Measure.measurable_map`. -/

end Equiv

abbrev ℝ_ (n : ℕ) := Fin n → ℝ

variable (lam : ℕ) {mean : (n : ℕ) → prod_iter_image (ℝ_ lam) (ℝ_ lam) n → ℝ}
  (hmean : ∀ n, Measurable <| mean n)
  {var : (n : ℕ) → prod_iter_image (ℝ_ lam) (ℝ_ lam) n → ℝ≥0}
  (hvar : ∀ n, Measurable <| var n)

lemma measurable_gaussianReal :
    Measurable (fun (p : ℝ × ℝ≥0) => gaussianReal p.1 p.2) := by
  rw [Measure.measurable_measure]
  intro s hs
  unfold gaussianReal
  simp_rw [DFunLike.ite_apply]
  refine Measurable.ite (by measurability) ?_ ?_
  · simp only [Measure.dirac_apply]
    exact Measurable.indicator measurable_const <| measurableSet_preimage measurable_fst hs
  · simp only [hs, withDensity_apply]
    refine Measurable.lintegral_prod_right <| Measurable.ennreal_ofReal ?_
    unfold gaussianPDFReal
    fun_prop

noncomputable def CMAKernel (n : ℕ) :
    Kernel (prod_iter_image (ℝ_ lam) (ℝ_ lam) n) (ℝ_ lam) where
  toFun data := Measure.pi (fun _ ↦ gaussianReal (mean n data) (var n data))
  measurable' := by
    refine .measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_pi.symm isPiSystem_pi ?_
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hs
    simp only [Measure.pi_pi]
    refine Finset.measurable_prod _ fun i hi ↦ ?_
    have measurable_gaussian := measurable_gaussianReal
    rw [Measure.measurable_measure] at measurable_gaussian
    specialize measurable_gaussian (t i) (ht i (Set.mem_univ _))
    exact measurable_gaussian.comp <| (hmean n).prodMk (hvar n)

variable (m : ℝ) (v : ℝ≥0)

/-- The _Covariance Matrix Adaptation - Evolution Strategy_ (CMA-ES) algorithm for global
optimization, given the mean and variance update rules as measurable functions of the history. -/
-- ANCHOR: CMA_ES
noncomputable def CMA_ES : Algorithm (ℝ_ lam) (ℝ_ lam) where
  ν := Measure.pi (fun _ ↦ gaussianReal m v)
  kernel_iter := CMAKernel lam hmean hvar
  markov_kernel n := ⟨fun a => by simp [CMAKernel]; infer_instance⟩
-- ANCHOR_END: CMA_ES

end
