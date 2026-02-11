/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanGO.Examples.Uniform
import LeanGO.Algorithm
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.CategoryTheory.Countable


open MeasureTheory ProbabilityTheory Set NNReal

/-!
# LIPO: Lipschitz Optimization
Implementation of the _Lipschitz Optimization_ algorithm defined on a measurable subset of a
Euclidean space, with finite and non-zero measure. The algorithm samples from the uniform
distribution on the set of potential maximizers of the function at each iteration.
-/

section Tuple

@[fun_prop]
lemma measurable_min {n : ℕ} : Measurable (fun (t : iter ℝ n) => Tuple.min t) := by
  unfold Tuple.min Fintype.min_image Fintype.min_image'
  have : Nonempty (Finset.Iic n) := inferInstance
  simp_all only [Finset.mem_Iic, nonempty_subtype, ↓reduceDIte, Finset.univ_eq_attach]
  fun_prop

@[fun_prop]
lemma measurable_max {n : ℕ} : Measurable (fun (t : iter ℝ n) => Tuple.max t) := by
  unfold Tuple.max Fintype.max_image Fintype.max_image'
  have : Nonempty (Finset.Iic n) := inferInstance
  simp_all only [Finset.mem_Iic, nonempty_subtype, ↓reduceDIte, Finset.univ_eq_attach]
  fun_prop

end Tuple

/-- Abbreviation for the Euclidean space of dimension `d`. -/
abbrev ED (d : ℕ) := EuclideanSpace ℝ (Fin d)

@[inherit_doc ED]
notation3 "ℝᵈ " d => ED d

namespace LIPO

variable {d : ℕ} {α : Set (ℝᵈ d)} (mes_α : MeasurableSet α) (mα₁ : ℙ α ≠ ⊤)

noncomputable instance : MeasureSpace α := Measure.Subtype.measureSpace

instance : MeasurableSpace α := by infer_instance

instance i₁ : IsFiniteMeasure (ℙ : Measure α) := by
  rw [isFiniteMeasure_iff ℙ, Measure.Subtype.volume_univ]
  · exact mα₁.lt_top
  · exact mes_α.nullMeasurableSet

variable {n : ℕ} (data : prod_iter_image α ℝ n) (κ : ℝ≥0)

def potential_max : Set α := {x | Tuple.max (data.2) ≤ Tuple.min
    (fun i => data.2 i + κ * dist (data.1 i) x)}

@[measurability]
lemma potential_max_measurable : MeasurableSet (potential_max data κ) :=
  measurableSet_le (by fun_prop) (by fun_prop)

@[measurability]
lemma potential_max_nullmeasurable : NullMeasurableSet (potential_max data κ) :=
  (potential_max_measurable data κ).nullMeasurableSet

example : 0 < ℙ (potential_max data κ) := by
  rw [Measure.Subtype.volume_def, Measure.comap_apply]
  · sorry
  · exact Subtype.val_injective
  · exact fun s a ↦ MeasurableSet.subtype_image mes_α a
  · measurability

noncomputable instance : MeasureSpace (potential_max data κ) := Measure.Subtype.measureSpace

instance : IsFiniteMeasure (ℙ : Measure (potential_max data κ)) := by
  rw [isFiniteMeasure_iff ℙ, Measure.Subtype.volume_univ]
  · have : potential_max data κ ⊆ univ := by simp
    refine lt_of_le_of_lt (measure_mono this) ?_
    rw [Measure.Subtype.volume_univ]
    · exact mα₁.lt_top
    · exact mes_α.nullMeasurableSet
  · exact (potential_max_nullmeasurable data κ)

@[measurability]
lemma measurableSet_potential_max_prod :
    MeasurableSet {p : prod_iter_image α ℝ n × α | p.2 ∈ potential_max p.1 κ} := by
  unfold potential_max
  simp only [mem_setOf_eq, measurableSet_setOf]
  refine Measurable.le' ?_ ?_
  · fun_prop
  · fun_prop

include mes_α mα₁ in
@[fun_prop]
lemma measurable_volume_potential_max_inter (s : Set α) (hs : MeasurableSet s) :
    Measurable (fun data : prod_iter_image α ℝ n => ℙ (potential_max data κ ∩ s)) := by
  set E := {p : prod_iter_image α ℝ n × α | p.2 ∈ potential_max p.1 κ ∩ s}
  have hE_meas : MeasurableSet E :=
    (measurableSet_potential_max_prod κ).inter (measurableSet_preimage measurable_snd hs)
  have := i₁ mes_α mα₁
  exact measurable_measure_prodMk_left hE_meas

noncomputable def potential_max_kernel : Kernel (prod_iter_image α ℝ n) α := by
  refine ⟨fun data => uniform <| potential_max data κ, ?_⟩
  rw [Measure.measurable_measure]
  intro s hs
  simp only [Measure.smul_apply, MeasureTheory.Measure.restrict_apply hs, smul_eq_mul]
  refine Measurable.mul ?_ ?_
  · refine Measurable.inv ?_
    convert measurable_volume_potential_max_inter mes_α mα₁ κ Set.univ (MeasurableSet.univ)
    simp [Set.inter_univ]
  · convert measurable_volume_potential_max_inter mes_α mα₁ κ s hs using 1
    simp [Set.inter_comm]

end LIPO

open LIPO

-- ANCHOR: LIPOvars
variable {d : ℕ} {κ : ℝ≥0} {α : Set (ℝᵈ d)} (mes_α : MeasurableSet α)
  (mα₀ : ℙ α ≠ 0) (mα₁ : ℙ α ≠ ⊤)
-- ANCHOR_END: LIPOvars

variable (h : ∀ n (data : prod_iter_image α ℝ n), ℙ (potential_max data κ) ≠ 0)

-- ANCHOR: LIPO
noncomputable def LIPO : Algorithm α ℝ where
  ν := uniform Set.univ
  prob_measure := by
    have := i₁ mes_α mα₁
    refine uniform_is_prob_measure ?_
    rwa [Measure.Subtype.volume_univ mes_α.nullMeasurableSet]
  kernel_iter _ := potential_max_kernel mes_α mα₁ κ
  markov_kernel n := by
    refine ⟨fun data => ?_⟩
    have := i₁ mes_α mα₁
    exact uniform_is_prob_measure <| h n data
-- ANCHOR_END: LIPO
