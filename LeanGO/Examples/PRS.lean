
/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanGO.Algorithm

open MeasureTheory ProbabilityTheory Set

/-!
# PRS: Pure Random Search

Implementation of the _Pure Random Search_ algorithm, which samples from a fixed probability
measure at each iteration.
-/

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
  [IsProbabilityMeasure μ]

/-- The Pure Random Search (PRS) algorithm for global optimization.
This baseline algorithm samples uniformly from the input space at each iteration using a fixed
probability measure `μ`. -/
-- ANCHOR: PRS
noncomputable def PRS : Algorithm α β where
  ν := μ
  kernel_iter _ := Kernel.const _ μ
-- ANCHOR_END: PRS
