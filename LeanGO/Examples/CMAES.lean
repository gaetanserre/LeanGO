/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanGO.Algorithm
public import Mathlib

@[expose] public section

open MeasureTheory ProbabilityTheory NNReal

/-!
# CMA-ES: Covariance Matrix Adaptation - Evolution Strategy

-/

variable (lam : ℕ)

abbrev R_lam := iter ℝ lam

variable {mean : (n : ℕ) → prod_iter_image (R_lam lam) ℝ n → ℝ}
  (hmean : ∀ n, Measurable <| mean n)
  {var : (n : ℕ) → prod_iter_image (R_lam lam) ℝ n → ℝ≥0}
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

noncomputable def gaussianKernel (n : ℕ) :
    Kernel (prod_iter_image (R_lam lam) ℝ n) (R_lam lam) where
  toFun data := Measure.pi (fun _ ↦ gaussianReal (mean n data) (var n data))
  measurable' := by
    have := measurable_gaussianReal.comp ((hmean n).prodMk (hvar n))
    sorry

noncomputable def CMA_ES : Algorithm (R_lam lam) ℝ where
  ν := Measure.pi (fun _ ↦ gaussianReal 0 1)
  kernel_iter := gaussianKernel lam hmean hvar
  markov_kernel n := ⟨fun a => by simp [gaussianKernel]; infer_instance⟩

end
