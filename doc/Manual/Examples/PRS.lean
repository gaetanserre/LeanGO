/-
 - Created in 2025 by Gaëtan Serré
-/

import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option pp.rawOnError true

set_option verso.exampleProject "../"

set_option verso.exampleModule "LeanGO.Examples.PRS"

#doc (Manual) "Pure Random Search" =>
%%%
htmlSplit := .never
%%%

The Pure Random Search (PRS) algorithm is a simple stochastic iterative global optimization algorithm that samples uniformly from the search space at each iteration. It can be represented in our framework as follows:

```anchor PRS
noncomputable def PRS : Algorithm α β where
  ν := uniform univ
  prob_measure := uniform_is_prob_measure (by simp [NeZero.ne ℙ])
  kernel_iter _ := Kernel.const _ (uniform (univ) : Measure α)
  markov_kernel _ := ⟨fun _ => uniform_is_prob_measure (by simp [NeZero.ne ℙ])⟩
```
