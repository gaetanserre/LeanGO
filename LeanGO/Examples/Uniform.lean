/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Mathlib.Probability.Notation

open MeasureTheory Set ProbabilityTheory

/-!
# Uniform distribution
This file defines the uniform distribution on a set of a finite measure space as the normalized
restriction of the original measure to the set.
-/

variable {α β : Type*} [MeasureSpace α] [IsFiniteMeasure (ℙ : Measure α)] [MeasurableSpace β]

noncomputable abbrev uniform (s : Set α) : Measure α := (ℙ s)⁻¹ • (ℙ).restrict s

instance uniform_is_prob_measure {s : Set α} (hs : ℙ s ≠ 0) : IsProbabilityMeasure (uniform s) := by
  rw [isProbabilityMeasure_iff]
  simp [ENNReal.inv_mul_cancel, hs]
