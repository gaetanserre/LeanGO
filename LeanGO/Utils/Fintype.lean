/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Lattice.Fold

namespace Fintype

variable {α β : Type*} [Fintype α] [LinearOrder β] (f : α → β)

def min_image' [i : Nonempty α] : β := Finset.univ.inf' (Finset.univ_nonempty_iff.mpr i) f

lemma le_min_image' [Nonempty α] : ∀ y, min_image' f ≤ f y :=
  fun y => Finset.inf'_le f (Finset.mem_univ y)

def max_image' [i : Nonempty α] : β := Finset.univ.sup' (Finset.univ_nonempty_iff.mpr i) f

lemma le_max_image' [Nonempty α] : ∀ y, f y ≤ max_image' f :=
  fun y => Finset.le_sup' f (Finset.mem_univ y)

variable [Nonempty β]

open Classical in
noncomputable def min_image : β :=
  if _ : Nonempty α then min_image' f
  else Classical.arbitrary β

lemma min_image_apply [Nonempty α] : min_image f = min_image' f := by
  unfold min_image
  split
  · rfl
  contradiction

lemma le_min_image [Nonempty α] : ∀ y, min_image f ≤ f y := by
  rw [min_image_apply]
  exact le_min_image' f

open Classical in
noncomputable def max_image : β :=
  if _ : Nonempty α then max_image' f
  else Classical.arbitrary β

lemma max_image_apply [Nonempty α] : max_image f = max_image' f := by
  unfold max_image
  split
  · rfl
  contradiction

lemma le_max_image [Nonempty α] : ∀ y, f y ≤ max_image f := by
  rw [max_image_apply]
  exact le_max_image' f

end Fintype
