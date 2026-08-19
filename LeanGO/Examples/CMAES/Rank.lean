/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

@[expose] public section

/-!
# Ranking a generation of CMA-ES

CMA-ES recombines the best points of each generation. As `LeanGO` maximizes objective functions,
a point is better than another one if its evaluation is greater, ties being broken by index.
Throughout, `evals` denotes the evaluations of the `λ` points of a generation.

## Main definitions

* `CMAES.rank`: the rank of a point of a generation, `0` being the rank of the best one.

## References

* [(_The CMA Evolution Strategy: A Tutorial_, Hansen, 2023)](https://arxiv.org/abs/1604.00772)
-/

namespace CMAES

open Finset

variable {lam : ℕ} (evals : Fin lam → ℝ)

/-- The `j`-th point of a generation is better than the `k`-th one if its evaluation is greater
or if both evaluations are equal and `j < k`. -/
-- ANCHOR: better
def better (j k : Fin lam) : Prop := evals k < evals j ∨ (evals j = evals k ∧ j < k)
-- ANCHOR_END: better

open scoped Classical in
/-- The rank of the `k`-th point of a generation, i.e. the number of points of that generation
that are `CMAES.better` than it. -/
-- ANCHOR: rank
noncomputable def rank (k : Fin lam) : ℕ := #{j | better evals j k}
-- ANCHOR_END: rank

open scoped Classical in
@[fun_prop]
lemma measurable_rank {α : Type*} [MeasurableSpace α] {evals : α → Fin lam → ℝ}
    (hevals : Measurable evals) (k : Fin lam) : Measurable fun a ↦ rank (evals a) k := by
  simp only [rank, Finset.card_filter]
  refine Finset.measurable_sum _ fun j _ ↦ ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  have hlt : MeasurableSet {a | evals a k < evals a j} := measurableSet_lt hevals.eval hevals.eval
  have heq : MeasurableSet {a | evals a j = evals a k ∧ j < k} := by
    by_cases h : j < k
    · simpa [h] using measurableSet_eq_fun (f := fun a ↦ evals a j) (g := fun a ↦ evals a k)
        hevals.eval hevals.eval
    · simp [h]
  simp only [better]
  exact hlt.union heq

end CMAES

end
