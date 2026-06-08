/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import LeanGO.Algorithm
public import LeanGO.Examples.ForMathlib.Multivariate

@[expose] public section

open MeasureTheory ProbabilityTheory

/-!
# CMA-ES: Covariance Matrix Adaptation - Evolution Strategy

A general implementation of the CMA-ES algorithm in any dimension. As CMA-ES
samples `λ` points at each iteration, the input space of the algorithm is `ℝ^(d × λ)`, which
represents a sequence of `λ` points in `ℝ^d`. The initial measure is the product of `λ` standard multivariate Gaussian measures on `ℝ^d`, and the kernel is defined as a product of `λ` multivariate Gaussian measures, where the mean and covariance are given by measurable functions of the past evaluations. These functions can be anything as long as they are measurable w.r.t. the history of the algorithm, thus allowing for any CMA-ES variant to be implemented in this framework.
-/

abbrev ℝ_ (d n : ℕ) := Fin n → EuclideanSpace ℝ (Fin d)

variable (d lam : ℕ)
  {mean : (n : ℕ) → prod_iter_image (ℝ_ d lam) (ℝ_ d lam) n → EuclideanSpace ℝ (Fin d)}
  (hmean : ∀ n, Measurable <| mean n)
  {covar : (n : ℕ) → prod_iter_image (ℝ_ d lam) (ℝ_ d lam) n → Matrix (Fin d) (Fin d) ℝ}
  (hcovar : ∀ n, Measurable <| covar n)

noncomputable def CMAKernel (n : ℕ) :
    Kernel (prod_iter_image (ℝ_ d lam) (ℝ_ d lam) n) (ℝ_ d lam) where
  toFun data := Measure.pi (fun _ ↦ multivariateGaussian (mean n data) (covar n data))
  measurable' := by
    refine .measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_pi.symm isPiSystem_pi ?_
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hs
    simp only [Measure.pi_pi]
    refine Finset.measurable_prod _ fun i hi ↦ ?_
    have measurable_gaussian := measurable_multivariateGaussian (ι := Fin d)
    rw [Measure.measurable_measure] at measurable_gaussian
    specialize measurable_gaussian (t i) (ht i (Set.mem_univ _))
    exact measurable_gaussian.comp <| (hmean n).prodMk (hcovar n)

variable (m : EuclideanSpace ℝ (Fin d)) (S : Matrix (Fin d) (Fin d) ℝ)

/-- The _Covariance Matrix Adaptation - Evolution Strategy_ (CMA-ES) algorithm for global
optimization, given the mean and covariance update rules as measurable functions of the history. -/
-- ANCHOR: CMA_ES
noncomputable def CMA_ES : Algorithm (ℝ_ d lam) (ℝ_ d lam) where
  ν := Measure.pi (fun _ ↦ multivariateGaussian m S)
  kernel_iter := CMAKernel d lam hmean hcovar
  markov_kernel n := ⟨fun a => by simp [CMAKernel]; infer_instance⟩
-- ANCHOR_END: CMA_ES

end
