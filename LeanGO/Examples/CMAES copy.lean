/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanGO.Algorithm
public import Mathlib
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

instance {ι γ α : Type*} [MeasurableSpace α] : MeasurableSpace (Matrix ι γ α) := by
  unfold Matrix
  infer_instance

end Equiv

lemma measurable_multivariateGaussian {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (multivariateGaussian (ι := ι)).uncurry := by
  unfold multivariateGaussian
  sorry

abbrev ℝ_ (d n : ℕ) := Fin n → EuclideanSpace ℝ (Fin d)

variable (d lam : ℕ)
  {mean : (n : ℕ) → prod_iter_image (ℝ_ d lam) (ℝ_ d lam) n → EuclideanSpace ℝ (Fin d)}
  (hmean : ∀ n, Measurable <| mean n)
  {var : (n : ℕ) → prod_iter_image (ℝ_ d lam) (ℝ_ d lam) n → Matrix (Fin d) (Fin d) ℝ}
  (hvar : ∀ n, Measurable <| var n)

noncomputable def CMAKernel (n : ℕ) :
    Kernel (prod_iter_image (ℝ_ d lam) (ℝ_ d lam) n) (ℝ_ d lam) where
  toFun data := Measure.pi (fun _ ↦ multivariateGaussian (mean n data) (var n data))
  measurable' := by
    refine .measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_pi.symm isPiSystem_pi ?_
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hs
    simp only [Measure.pi_pi]
    refine Finset.measurable_prod _ fun i hi ↦ ?_
    --sorry
    have measurable_gaussian := measurable_multivariateGaussian (ι := Fin d)
    rw [Measure.measurable_measure] at measurable_gaussian
    specialize measurable_gaussian (t i) (ht i (Set.mem_univ _))
    exact measurable_gaussian.comp <| (hmean n).prodMk (hvar n)

variable (m : EuclideanSpace ℝ (Fin d)) (v : Matrix (Fin d) (Fin d) ℝ)

/-- The _Covariance Matrix Adaptation - Evolution Strategy_ (CMA-ES) algorithm for global
optimization, given the mean and variance update rules as measurable functions of the history. -/
-- ANCHOR: CMA_ES
noncomputable def CMA_ES : Algorithm (ℝ_ d lam) (ℝ_ d lam) where
  ν := Measure.pi (fun _ ↦ multivariateGaussian m v)
  kernel_iter := CMAKernel d lam hmean hvar
  markov_kernel n := ⟨fun a => by simp [CMAKernel]; infer_instance⟩
-- ANCHOR_END: CMA_ES

end
