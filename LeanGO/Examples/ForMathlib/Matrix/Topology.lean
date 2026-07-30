module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

@[expose] public section

open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

namespace Matrix

@[fun_prop]
lemma continuousOn_cfcSqrt_nonneg : ContinuousOn (CFC.sqrt) {S : Matrix ι ι ℝ | 0 ≤ S} :=
  CFC.continuousOn_sqrt

instance : OrderClosedTopology (Matrix ι ι ℝ) where
  isClosed_le' := by
    refine IsClosed.preimage (by fun_prop) (t := {M : Matrix ι ι ℝ | Matrix.PosSemidef M}) ?_
    simp only [PosSemidef, star_trivial, Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter ?_ <| isClosed_iInter (fun f ↦ isClosed_le continuous_const ?_)
    · exact isClosed_eq continuous_id.matrix_transpose continuous_id
    · exact continuous_finsetSum _ fun i hi ↦ continuous_finsetSum _ (fun k hk ↦ by fun_prop)

end Matrix
