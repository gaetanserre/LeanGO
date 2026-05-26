/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

@[expose] public section

open Set

namespace MeasureTheory.Measure

variable {ι : Type*} [Finite ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
  {μ ν : Measure (∀ i, α i)} [IsFiniteMeasure μ]

/-- Two finite measures on a finite product space are equal if they agree on all measurable
rectangles of the form `univ.pi s`. -/
lemma pi_space_eq
    (h : ∀ s : ∀ i, Set (α i), (∀ i, MeasurableSet (s i)) → μ (univ.pi s) = ν (univ.pi s)) :
    μ = ν := by
  refine ext_of_generate_finite _ generateFrom_pi.symm isPiSystem_pi ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    exact h s (mem_univ_pi.mp hs)
  · have := h (fun i ↦ (univ : Set (α i))) (fun i => MeasurableSet.univ)
    convert this
    <;> simp

end MeasureTheory.Measure
