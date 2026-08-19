module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Measurable
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

open Matrix ProbabilityTheory MeasureTheory

open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[fun_prop]
lemma measurable_matrix_inv : Measurable (fun M : Matrix ι ι ℝ ↦ M⁻¹) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  refine Measurable.smul (M := ℝ) (α := Matrix ι ι ℝ) ?_ ?_
  · exact (Continuous.matrix_det continuous_id).measurable.inv
  · exact (Continuous.matrix_adjugate continuous_id).measurable

@[fun_prop]
lemma measurable_toEuclideanCLM :
    Measurable (fun (S, x) ↦ toEuclideanCLM (n := ι) (𝕜 := ℝ) S x) := by
  apply Continuous.measurable
  refine Continuous.comp ?_ <| continuous_pi fun i ↦ ?_
  · fun_prop
  · simp
    fun_prop

@[fun_prop]
lemma measurable_multivariateGaussian : Measurable (multivariateGaussian (ι := ι)).uncurry := by
  rw [Measure.measurable_measure]
  intro s hs
  simp [Function.uncurry, multivariateGaussian]
  conv =>
    rhs
    intro b
    rw [Measure.map_apply (by fun_prop) hs]
  let A := {((μ, S), x) | μ + toEuclideanCLM ( 𝕜 := ℝ ) ( CFC.sqrt S ) x ∈ s}
  have := CFC.measurable_sqrt (A := Matrix ι ι ℝ)
  exact measurable_measure_prodMk_left (s := A) <| hs.preimage (by fun_prop)
