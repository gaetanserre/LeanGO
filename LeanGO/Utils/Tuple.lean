/-
 - Created in 2025 by Gaëtan Serré
-/

import LeanGO.Utils.Iter
import LeanGO.Utils.Fintype
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

open Set

variable {α : Type*}

namespace Tuple

noncomputable def min [LinearOrder α] [Nonempty α] {n : ℕ} (f : iter α n) := Fintype.min_image f


instance {n : ℕ} : Nonempty (Finset.Iic n) := Nonempty.intro ⟨0, Finset.insert_eq_self.mp rfl⟩

lemma le_min [LinearOrder α] [Nonempty α] {n : ℕ} (f : iter α n) : ∀ j, min f ≤ f j := by
  haveI : Nonempty (Fin (n + 1)) := instNonemptyOfInhabited
  exact Fintype.le_min_image f

noncomputable def max [LinearOrder α] [Nonempty α] {n : ℕ} (f : iter α n) := Fintype.max_image f

lemma le_max [LinearOrder α] [Nonempty α] {n : ℕ} (f : iter α n) : ∀ j, f j ≤ max f := by
  haveI : Nonempty (Fin (n + 1)) := instNonemptyOfInhabited
  exact Fintype.le_max_image f

variable {β : Type*}

lemma mem_iic_le {n m x : ℕ} (hnm : n ≤ m) (h : x ∈ Finset.Iic n) : x ∈ Finset.Iic m :=
  Finset.mem_Iic.mpr <| le_trans (Finset.mem_Iic.mp h) hnm

/-- Given `n ≤ m`, this is the restriction of a function `u : iter α m`
to a function `iter α n`. -/
abbrev subTuple {n m : ℕ} (hnm : n ≤ m) (u : iter α m) : iter α n :=
  fun i => u ⟨i.1, mem_iic_le hnm i.2⟩


/-- Given `n`, a function `f : α → β` and a function `u : iter α n`,
this is the pair `(u, f ∘ u)`, where `f ∘ u` is the function
from `Fin (n + 1)` to `β` that applies `f` to the values of `u`. -/
abbrev prod_eval (n : ℕ) (f : α → β) (u : iter α n) := (u, f ∘ u)

/-- Given a set `s` and two functions `f g : α → β`, such that `f` and `g` are equal on `s`,
the pair `(u, f ∘ u)` is equal to the pair `(u, g ∘ u)` for any `u : iter α n`
such that `u i ∈ s` for all `i`. -/
lemma prod_eval_eq_restrict (n : ℕ) {f g : α → β} {s : Set α} (hfg : s.EqOn f g)
    {u : iter α n} (hu : ∀ i, u i ∈ s) : prod_eval n f u = prod_eval n g u := by
  ext i
  · rfl
  · specialize hu i
    simp_all only [Function.comp_apply]
    have fwd : f (u i) = g (u i) := EqOn.eq_of_mem hfg hu
    exact fwd

/-- For any measurable function `f : α → β`, the function `prod_eval n f` is measurable. -/
lemma measurable_prod_eval [MeasurableSpace α] [MeasurableSpace β] (n : ℕ)
    {f : α → β} (hf : Measurable f) : Measurable (prod_eval n f) := by
  refine Measurable.prodMk measurable_id ?_
  unfold Function.comp
  apply measurable_pi_lambda
  intro a
  apply Measurable.comp
  · exact hf
  · exact measurable_pi_apply _

variable [LinearOrder β] [Nonempty β] (f : α → β)

lemma argmin {n : ℕ} (u : iter α n) : ∃ i, f (u i) = min (f ∘ u) := by
  haveI : Nonempty (Finset.Iic n) := inferInstance
  unfold min Fintype.min_image
  split
  swap
  · contradiction
  unfold Fintype.min_image'
  have univ_ne : (Finset.univ : Finset (Finset.Iic n)).Nonempty := Finset.univ_nonempty_iff.mpr this
  let A := {x | ∃ i, u i = x}
  suffices h : Finset.univ.inf' univ_ne (f ∘ u) ∈ (f '' A) by
    obtain ⟨x, ⟨i, hi⟩, h⟩ := h
    rw [← h, ←hi]
    use i
  have min_mem : ∀ x ∈ (f '' A), ∀ y ∈ (f '' A), x ⊓ y ∈ (f '' A) := by
    intro x hx y hy
    cases min_choice x y with
    | inl inl => rwa [inl]
    | inr inr => rwa [inr]
  apply Finset.inf'_mem (f '' A) min_mem Finset.univ univ_ne (f ∘ u)
  intro i _
  exact ⟨u i, ⟨i, rfl⟩, rfl⟩

lemma argmax {n : ℕ} (u : iter α n) : ∃ i, f (u i) = max (f ∘ u) := by
  haveI : Nonempty (Finset.Iic n) := inferInstance
  unfold max Fintype.max_image
  split
  swap
  · contradiction
  unfold Fintype.max_image'
  have univ_ne : (Finset.univ : Finset (Finset.Iic n)).Nonempty := Finset.univ_nonempty_iff.mpr this
  let A := {x | ∃ i, u i = x}
  suffices h : Finset.univ.sup' univ_ne (f ∘ u) ∈ (f '' A) by
    obtain ⟨x, ⟨i, hi⟩, h⟩ := h
    rw [← h, ←hi]
    use i
  have max_mem : ∀ x ∈ (f '' A), ∀ y ∈ (f '' A), x ⊔ y ∈ (f '' A) := by
    intro x hx y hy
    cases max_choice x y with
    | inl inl => rwa [inl]
    | inr inr => rwa [inr]
  apply Finset.sup'_mem (f '' A) max_mem Finset.univ univ_ne (f ∘ u)
  intro i _
  exact ⟨u i, ⟨i, rfl⟩, rfl⟩

end Tuple
