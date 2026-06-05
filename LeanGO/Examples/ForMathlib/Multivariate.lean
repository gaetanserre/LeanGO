module

public import LeanGO.Examples.ForMathlib.Matrix.Measurable
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

open Matrix ProbabilityTheory MeasureTheory

open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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
  exact measurable_measure_prodMk_left (s := A) <| hs.preimage (by fun_prop)
