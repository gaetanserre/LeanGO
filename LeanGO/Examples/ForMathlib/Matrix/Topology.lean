module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

@[expose] public section

open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Matrix

@[fun_prop]
lemma continuousOn_cfcSqrt_nonneg : ContinuousOn (CFC.sqrt) {S : Matrix ι ι ℝ | 0 ≤ S} :=
  CFC.continuousOn_sqrt

end Matrix
