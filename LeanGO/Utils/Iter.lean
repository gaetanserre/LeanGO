/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-- `iter α n` is the type of finite sequences of elements in `α` of length `n + 1`.

It represents the history of `n + 1` steps in an iterative process,
with entries indexed by `Fin (n + 1)` (i.e., from `0` to `n`).

Used in the context of stochastic iterative algorithms to store past evaluations or points. -/
abbrev iter (α : Type*) (n : ℕ) := Π _ : Finset.Iic n, α

/- abbrev to_iter {α : Type*} (n : ℕ) (u : ℕ → α) : iter α n := fun i => u i

def from_iter_set {α : Type*} {n : ℕ} (s : Set (iter α n)) : Set (ℕ → α) :=
  {u | to_iter n u ∈ s}

lemma from_iter_set_subset {α : Type*} {n : ℕ} {s₁ s₂ : Set (iter α n)} (h : s₁ ⊆ s₂) :
  from_iter_set s₁ ⊆ from_iter_set s₂ := by
  intro u hu
  simp only [from_iter_set] at hu
  exact h hu

open Set in
lemma biUinion_from_iter {α ι : Type*} {n : ℕ} (I : Finset ι) (s : ι → Set (iter α n)) :
  from_iter_set (⋃ i ∈ I, s i) = ⋃ i ∈ I, from_iter_set (s i) := by
  ext u
  simp only [from_iter_set, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨i, hi, hu⟩
    exact ⟨i, hi, hu⟩
  · rintro ⟨i, hi, hu⟩
    exact ⟨i, hi, hu⟩ -/

/-- `prod_iter_image α β n` is the input space of the algorithm at iteration `n`.

It consists of:
- a sequence of `n + 1` past points in `α`,
- and their corresponding evaluations in `β`.

This pair encodes the full information available up to iteration `n`. -/
-- ANCHOR: prod_iter_image
abbrev prod_iter_image (α β : Type*) (n : ℕ) := (iter α n) × (iter β n)
-- ANCHOR_END: prod_iter_image

/- `iter_mequiv α n` is a measurable equivalence between `iter α (n + 1)` and `α × iter α n`.

This equivalence decomposes a sequence of length `n + 2` (indexed by `Fin (n + 2)`)
into its last element and the remaining sequence of length `n + 1`.

Specifically, it maps a function `f : Fin (n + 2) → α` to the pair `(f (Fin.last (n + 1)), g)`
where `g : Fin (n + 1) → α` is defined by `g i = f (Fin.castSucc i)`.

This is useful for inductive constructions on iterative sequences, allowing to separate
the "current" step from the "history" of previous steps. -/
/- def iter_mequiv (α : Type*) [MeasurableSpace α] (n : ℕ) : iter α (n + 1) ≃ᵐ iter α n × α :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => α) (Fin.last (n + 1))).trans MeasurableEquiv.prodComm -/
