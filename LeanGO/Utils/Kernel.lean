/-
 - Created in 2025 by Gaëtan Serré
-/

import LeanGO.Utils.Tuple
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj

open MeasureTheory

namespace ProbabilityTheory.Kernel

section avg

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (κ : Kernel α β) (μ : Measure α)

/-- The average of a kernel `κ` by a measure `μ`. Defined as `s↦ ∫⁻ a, κ a s ∂μ` -/
noncomputable def avg : Measure β := by
  refine Measure.ofMeasurable (fun s hs => ∫⁻ a, κ a s ∂μ) ?_ ?_
  · simp only [measure_empty, MeasureTheory.lintegral_const, zero_mul]
  · intro f f_m f_d
    simp_rw [fun x => measure_iUnion f_d f_m]
    exact lintegral_tsum (fun i => (κ.measurable_coe <| f_m i).aemeasurable)

@[simp]
lemma avg_apply {s : Set β} (hs : MeasurableSet s) : (avg κ μ) s = ∫⁻ a, κ a s ∂μ := by
  rw [avg, Measure.ofMeasurable_apply _ hs]

instance [IsMarkovKernel κ] [IsProbabilityMeasure μ] : IsProbabilityMeasure (κ.avg μ) := by
  rw [isProbabilityMeasure_iff]
  simp only [MeasurableSet.univ, avg_apply, measure_univ, MeasureTheory.lintegral_const, mul_one]

end avg

section rect

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1))) {a b : ℕ}
  (hab : a ≤ b) [∀ n, IsMarkovKernel (κ n)] (μ : Measure (Π i : Finset.Iic a, X i))

open Set Function Tuple

lemma partialTraj_avg_rect_eq {C : (i : Finset.Iic b) → Set (X i)} (hC : ∀ i, MeasurableSet (C i)) :
    (partialTraj κ a b).avg μ (univ.pi C) =
    ∫⁻ u in univ.pi (fun (i : Finset.Iic a) => C ⟨i.1, mem_iic_le hab i.2⟩),
      (partialTraj κ a b) u (univ.pi C) ∂μ := by
  have measure_pi_C : MeasurableSet (univ.pi C) := MeasurableSet.univ_pi hC
  rw [Kernel.avg_apply _ _ measure_pi_C]
  rw [← lintegral_indicator (MeasurableSet.univ_pi fun i ↦ hC ⟨i.1, mem_iic_le hab i.2⟩) _]
  congr with u
  by_cases hu : u ∈ univ.pi (fun (i : Finset.Iic a) => C ⟨i.1, mem_iic_le hab i.2⟩)
  · simp [hu]
  · simp only [hu, not_false_eq_true, indicator_of_notMem]
    rw [← lintegral_indicator_one measure_pi_C]
    rw [partialTraj_eq_prod, lintegral_map, lintegral_id_prod, lintegral_map]
    · simp only [IicProdIoc_def, Finset.restrict₂]
      suffices ∀ (x : Π i : Finset.Iic b, X i),
          (fun (i : Finset.Iic b) ↦
          if h : i.1 ≤ a then u ⟨i.1, Finset.mem_Iic.mpr h⟩
          else x i) ∉ univ.pi C by
        simp [this]
      intro x x_mem
      simp_all only [Subtype.forall, Finset.mem_Iic, mem_pi, not_forall]
      obtain ⟨i, hi, -, hui⟩ := hu
      specialize x_mem i (Nat.le_trans hi hab) trivial
      simp_all only [↓reduceDIte]
    · fun_prop
    · refine Measurable.indicator measurable_const ?_
      have m_Iic_prod : Measurable (fun x => IicProdIoc a b (u, x)) := by fun_prop
      exact m_Iic_prod measure_pi_C
    · refine Measurable.indicator measurable_const ?_
      have m_Iic_prod : Measurable (fun (x : (Π i : Finset.Iic a, X i) ×
          (Π i : Finset.Ioc a b, X i)) => IicProdIoc a b x) := by fun_prop
      exact m_Iic_prod measure_pi_C
    · fun_prop
    · exact Measurable.indicator measurable_const measure_pi_C

end rect

section restrict

open Finset

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)] {a b : ℕ}
  {κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))}

/-- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Ionescu-Tulcea.20partialTraj.20restrictions -/
lemma partialTraj_restrict {s : Π n, Set (X n)} [∀ n, IsSFiniteKernel (κ n)]
    (hs : ∀ n, MeasurableSet (s n)) (hab : a ≤ b) {x : Π i : Iic a, X i}
    (hx : x ∈ Set.univ.pi (fun i : Iic a ↦ s i)) :
    partialTraj (fun n ↦ (κ n).restrict (hs (n + 1))) a b x =
    (partialTraj κ a b x).restrict (Set.univ.pi (fun i ↦ s i)) := by
  induction b, hab using Nat.le_induction with
  | base =>
    simp only [partialTraj_self, id_apply]
    classical
    rw [restrict_dirac', if_pos hx]
    exact MeasurableSet.univ_pi fun i ↦ hs ↑i
  | succ b hab hb =>
    ext t ht
    rw [partialTraj_succ_eq_comp hab, Kernel.comp_apply' _ _ _ ht, hb, Measure.restrict_apply ht,
      partialTraj_succ_eq_comp hab, Kernel.comp_apply',
      ← lintegral_add_compl (μ := partialTraj κ a b x) _ (.univ_pi fun i ↦ hs i),
      ← add_zero (∫⁻ _, _ ∂_)]
    · have m_inter_t_pi := (ht.inter (MeasurableSet.univ_pi fun i ↦ hs i))
      congrm ?_ + ?_
      · refine setLIntegral_congr_fun (.univ_pi fun i ↦ hs i) fun y hy ↦ ?_
        simp_rw [partialTraj_succ_self]
        rw [Kernel.map_apply', Kernel.id_prod_apply', Kernel.map_apply', Kernel.restrict_apply',
          Kernel.map_apply', Kernel.id_prod_apply', Kernel.map_apply']
        · congr 2
          ext z
          change _ ↔
            IicProdIoc b (b + 1) (y, MeasurableEquiv.piSingleton b z) ∈ Set.univ.pi (fun _ ↦ s _)
          simp only [MeasurableEquiv.piSingleton, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
            Set.mem_pi, Set.mem_univ, IicProdIoc, forall_const, Subtype.forall, mem_Iic]
          constructor
          · intro h i hi
            split_ifs with h'
            · simp only [Set.mem_pi, Set.mem_univ, forall_const, Subtype.forall, mem_Iic] at hy
              exact hy i h'
            obtain rfl : i = b + 1 := by omega
            exact h
          · intro h
            convert h (b + 1) le_rfl
            simp
        any_goals fun_prop
        · exact measurableSet_preimage (by fun_prop)
            <| measurableSet_preimage (by fun_prop) m_inter_t_pi
        · exact measurableSet_preimage (by fun_prop) m_inter_t_pi
        · exact m_inter_t_pi
        · refine (MeasurableEquiv.piSingleton b).measurableSet_preimage.mpr ?_
          exact measurableSet_preimage (by fun_prop) <| measurableSet_preimage (by fun_prop) ht
        · exact measurableSet_preimage (by fun_prop) <| measurableSet_preimage (by fun_prop) ht
        · exact measurableSet_preimage (by fun_prop) ht
        · exact ht
      · symm
        apply setLIntegral_eq_zero
        · exact .compl (.univ_pi fun _ ↦ hs _)
        intro y hy
        simp only [Pi.zero_apply]
        rw [partialTraj_succ_self, Kernel.map_apply', Kernel.id_prod_apply', Kernel.map_apply']
        · convert measure_empty
          · ext z
            simp only [MeasurableEquiv.piSingleton, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
              Set.preimage_inter, Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
              IicProdIoc, forall_const, Subtype.forall, mem_Iic, Set.mem_empty_iff_false, iff_false,
              not_and, not_forall]
            intro h1
            simp only [Set.mem_compl_iff, Set.mem_pi, Set.mem_univ, forall_const, Subtype.forall,
              mem_Iic, not_forall] at hy
            obtain ⟨i, hi1, hi2⟩ := hy
            refine ⟨i, by omega, ?_⟩
            simpa [hi1]
          infer_instance
        · exact (MeasurableEquiv.piSingleton b).measurable
        · suffices Measurable (IicProdIoc b (b + 1) ∘ (Prod.mk y)) from
            this m_inter_t_pi
          fun_prop
        · suffices Measurable (IicProdIoc b (b + 1)) from
            this m_inter_t_pi
          fun_prop
        · fun_prop
        · exact m_inter_t_pi
    · exact ht.inter (.univ_pi fun _ ↦ hs _)

open Set

variable {α : Type*} [MeasurableSpace α]
  {κ₁ κ₂ : (n : ℕ) → Kernel (Π _ : Finset.Iic n, α) α}
  [∀ n, IsMarkovKernel (κ₁ n)] [∀ n, IsMarkovKernel (κ₂ n)] {s : Π (_ : ℕ), Set α}

lemma partialTraj_restrict' {a b : ℕ} (hab : a ≤ b) (hs : ∀ n, MeasurableSet (s n))
    (h : ∀ n,
      (Set.univ.pi (fun (i : Finset.Iic n) => s i)).EqOn (fun a => κ₁ n a) (fun a => κ₂ n a)) :
    (univ.pi (fun (i : Finset.Iic a) => s i)).EqOn
    (fun e => (Kernel.partialTraj (X := fun _ => α) κ₁ a b e).restrict (univ.pi (fun i => s i)))
    (fun e => (Kernel.partialTraj (X := fun _ => α) κ₂ a b e).restrict (univ.pi (fun i => s i)))
    := by
  intro e he
  simp_rw [← Kernel.partialTraj_restrict (fun n => hs n) hab he]
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab hb =>
    simp only [Kernel.partialTraj_succ_eq_comp hab, comp_apply]
    rw [hb]
    ext t ht
    simp_rw [Measure.bind_apply ht (Kernel.aemeasurable _),
      Kernel.partialTraj_restrict (fun n => hs n) hab he]
    suffices (univ.pi (fun (i : Finset.Iic b) => s i)).EqOn
        (fun a => partialTraj (X := fun _ => α)
          (fun n ↦ (κ₁ n).restrict (hs (n + 1))) b (b + 1) a t)
        (fun a => partialTraj (X := fun _ => α)
          (fun n ↦ (κ₂ n).restrict (hs (n + 1))) b (b + 1) a t) by
      rw [setLIntegral_congr_fun (by exact MeasurableSet.univ_pi fun i ↦ hs ↑i) this]
    intro a a_mem
    simp only [partialTraj_succ_self]
    rw [Kernel.map_apply' _ (by exact measurable_IicProdIoc),
      Kernel.map_apply' _ (by exact measurable_IicProdIoc),
      Kernel.id_prod_apply', Kernel.id_prod_apply',
      Kernel.map_apply', Kernel.map_apply',
      Kernel.restrict_apply', Kernel.restrict_apply']
    · simp_rw [h b a_mem]
    any_goals fun_prop
    · exact measurableSet_preimage (by fun_prop) <| measurableSet_preimage (by fun_prop)
      <| measurableSet_preimage (measurable_IicProdIoc) ht
    · exact measurableSet_preimage (by fun_prop) <| measurableSet_preimage (by fun_prop)
      <| measurableSet_preimage (measurable_IicProdIoc) ht
    · exact measurableSet_preimage (by fun_prop) <| measurableSet_preimage (measurable_IicProdIoc)
        ht
    · exact measurableSet_preimage (by fun_prop) <| measurableSet_preimage (measurable_IicProdIoc)
        ht
    · exact measurableSet_preimage (measurable_IicProdIoc) ht
    · exact measurableSet_preimage (measurable_IicProdIoc) ht
    any_goals exact ht

end restrict

end ProbabilityTheory.Kernel
