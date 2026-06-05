module

public import LeanGO.Examples.ForMathlib.Matrix.Topology
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open scoped MatrixOrder Matrix.Norms.L2Operator

@[expose] public section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Matrix

instance : MeasurableSpace (Matrix ι ι ℝ) := inferInstanceAs <| MeasurableSpace (ι → ι → ℝ)

instance : BorelSpace (Matrix ι ι ℝ) := inferInstanceAs <| BorelSpace (ι → ι → ℝ)

@[fun_prop]
lemma measurable_cfcSqrt_matrix :
    Measurable (CFC.sqrt : Matrix ι ι ℝ → Matrix ι ι ℝ) := by
  have h_measurable : MeasurableSet {S : Matrix ι ι ℝ | 0 ≤ S} := by
    apply IsClosed.measurableSet
    convert IsClosed.isClosed_le (α := Matrix ι ι ℝ) (f := 0) (g := id) isClosed_univ ?_ ?_
    · simp
    · exact continuous_const.continuousOn
    · exact continuous_id.continuousOn
  convert continuousOn_cfcSqrt_nonneg.measurable_piecewise continuousOn_const h_measurable using 1
  rotate_left
  · exact fun _ => Classical.dec _
  · exact 0
  · ext S : 1
    by_cases hS : 0 ≤ S
    · simp [hS]
    · simp [hS, CFC.sqrt_of_not_nonneg]

end Matrix
