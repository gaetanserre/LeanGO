/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanGO.Utils.Tuple
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.CategoryTheory.Countable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory

section Tuple

/- @[fun_prop]
lemma measurable_min {n : ℕ} : Measurable (fun (t : iter ℝ n) => Tuple.min t) := by
  unfold Tuple.min Fintype.min_image Fintype.min_image'
  have : Nonempty (Finset.Iic n) := inferInstance
  simp_all only [Finset.mem_Iic, nonempty_subtype, ↓reduceDIte, Finset.univ_eq_attach]
  fun_prop

@[fun_prop]
lemma measurable_max {n : ℕ} : Measurable (fun (t : iter ℝ n) => Tuple.max t) := by
  unfold Tuple.max Fintype.max_image Fintype.max_image'
  have : Nonempty (Finset.Iic n) := inferInstance
  simp_all only [Finset.mem_Iic, nonempty_subtype, ↓reduceDIte, Finset.univ_eq_attach]
  fun_prop -/

end Tuple

/-- Euclidean space of dimension `d`.
Used as the domain for LIPO optimization problems. -/
abbrev ED (d : ℕ) := EuclideanSpace ℝ (Fin d)

@[inherit_doc ED]
notation3 "ℝᵈ " d => ED d
