module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

@[expose] public section

open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

namespace Matrix

lemma l2_opNorm_unitary_conj (U : unitary (Matrix ι ι 𝕜)) (A : Matrix ι ι 𝕜) :
    ‖U * A * (star (U : Matrix ι ι 𝕜))‖ = ‖A‖ := by
  simpa [mul_assoc, CStarRing.norm_coe_unitary_mul] using
    CStarRing.norm_mul_coe_unitary A (star U)

lemma l2_opNorm_eq_pi_norm {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) (f : C((spectrum ℝ A), ℝ)) :
    ‖RCLike.ofReal (K := 𝕜) ∘ f ∘ fun i ↦ ⟨hA.eigenvalues i, hA.eigenvalues_mem_spectrum_real i⟩‖
      = ‖f‖ := by
  refine le_antisymm ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    simp only [Function.comp_apply, norm_algebraMap']
    exact f.norm_coe_le_norm _
  · rw [ContinuousMap.norm_le _ (by positivity)]
    intro x
    apply Real.toNNReal_le_iff_le_coe.mp
    obtain ⟨i, hi⟩ : ∃ i : ι, x = ⟨hA.eigenvalues i, hA.eigenvalues_mem_spectrum_real i⟩ := by
      have := hA.spectrum_real_eq_range_eigenvalues
      grind
    rw [hi]
    convert Finset.le_sup (b := i) (Finset.mem_univ _)
    simp only [Real.norm_eq_abs, Real.toNNReal_abs, Function.comp_apply, nnnorm_algebraMap']
    rfl

lemma l2_opNorm_eq_diagonal_norm {A : Matrix ι ι 𝕜} (hA : A.IsHermitian)
    (f : C((spectrum ℝ A), ℝ)) : ‖diagonal <| RCLike.ofReal (K := 𝕜) ∘
      f ∘ fun i ↦ ⟨hA.eigenvalues i, hA.eigenvalues_mem_spectrum_real i⟩‖ = ‖f‖ := by
    rw [l2_opNorm_diagonal]
    exact l2_opNorm_eq_pi_norm hA f

set_option backward.isDefEq.respectTransparency false in
instance : IsometricContinuousFunctionalCalculus ℝ (Matrix ι ι 𝕜) IsSelfAdjoint where
  predicate_zero := by simp
  spectrum_nonempty := ContinuousFunctionalCalculus.spectrum_nonempty
  exists_cfc_of_predicate := ContinuousFunctionalCalculus.exists_cfc_of_predicate
  isometric A hA := by
    rw [← isHermitian_iff_isSelfAdjoint] at hA
    rw [IsHermitian.cfcHom_eq_cfcAux hA, AddMonoidHomClass.isometry_iff_norm]
    intro f
    simp only [IsHermitian.cfcAux_apply, Unitary.conjStarAlgAut_apply]
    convert l2_opNorm_unitary_conj _ _
    exact (l2_opNorm_eq_diagonal_norm hA f).symm

@[fun_prop]
lemma continuousOn_cfcSqrt_nonneg : ContinuousOn (CFC.sqrt) {S : Matrix ι ι ℝ | 0 ≤ S} :=
  CFC.continuousOn_sqrt

instance : OrderClosedTopology (Matrix ι ι ℝ) where
  isClosed_le' := by
    refine IsClosed.preimage (by fun_prop) (t := {M : Matrix ι ι ℝ | Matrix.PosSemidef M}) ?_
    simp only [PosSemidef, star_trivial, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter ?_ <| isClosed_iInter (fun f ↦ isClosed_le continuous_const ?_)
    · refine isClosed_eq ?_ continuous_id
      exact continuous_id.matrix_transpose
    · refine continuous_finsetSum _ fun i hi ↦ continuous_finsetSum _ (fun k hk ↦ ?_)
      fun_prop

end Matrix
