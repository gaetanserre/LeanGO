/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-- `iter α n` is the type of finite sequences of elements in `α` of length `n + 1`.

It represents the history of `n + 1` steps in an iterative process,
with entries indexed by `Fin (n + 1)` (i.e., from `0` to `n`).

Used in the context of stochastic iterative algorithms to store past evaluations or points. -/
abbrev iter (α : Type*) (n : ℕ) := Π _ : Finset.Iic n, α

/-- `prod_iter_image α β n` is the input space of the algorithm at iteration `n`.

It consists of:
- a sequence of `n + 1` past points in `α`,
- and their corresponding evaluations in `β`.

This pair encodes the full information available up to iteration `n`. -/
-- ANCHOR: prod_iter_image
abbrev prod_iter_image (α β : Type*) (n : ℕ) := (iter α n) × (iter β n)
-- ANCHOR_END: prod_iter_image

variable {α β : Type*}

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
    have fwd : f (u i) = g (u i) := hfg.eq_of_mem hu
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
