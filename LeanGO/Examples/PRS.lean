
/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanGO.Algorithm
import LeanGO.Examples.Uniform

open MeasureTheory ProbabilityTheory Set

/-!
# PRS: Pure Random Search
Implementation of the _Pure Random Search_ algorithm, which samples from the uniform
distribution on the input space at each iteration.
-/

variable {α β : Type*} [MeasureSpace α] [IsFiniteMeasure (ℙ : Measure α)]
  [NeZero (ℙ : Measure α)] [MeasurableSpace β]

/-- The Pure Random Search (PRS) algorithm for global optimization.
This baseline algorithm samples uniformly from the input space at each iteration,
independently of past observations. It serves as a reference benchmark for comparing
more sophisticated optimization strategies. -/
-- ANCHOR: PRS
noncomputable def PRS : Algorithm α β where
  ν := uniform univ
  prob_measure := uniform_is_prob_measure (by simp [NeZero.ne ℙ])
  kernel_iter _ := Kernel.const _ (uniform (univ) : Measure α)
  markov_kernel _ := ⟨fun _ => uniform_is_prob_measure (by simp [NeZero.ne ℙ])⟩
-- ANCHOR_END: PRS
