/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanGO.Examples.Decision

/-!
# RankOpt: A Ranking Approach to Global Optimization

Implementation of the _RankOpt_ algorithm
[(_A Ranking Approach to Global Optimization_,
Malherbe et al. 2017)](https://arxiv.org/abs/1603.04381)
defined on a measurable space. The algorithm samples from an arbitrary probability measure
on the set of potential maximizers of the function at each iteration. It is defined as a special
case of the `Decision` algorithm.

## Main definitions

* `RankRule`: A rank rule is a measurable function that compares pairs of points.
  It returns 1 if the first point is ranked higher, -1 if lower, and 0 if equal.
* `potential_max`: The set of potential maximizers for the RankOpt algorithm.
* `RankOpt`: The RankOpt algorithm that samples from the set of potential maximizers using a given
  probability measure at each iteration.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset NNReal

section RankRule

/-- A rank rule is a measurable function that compares pairs of points.
It returns 1 if the first point is ranked higher, -1 if lower, and 0 if equal. -/
-- ANCHOR: RankRule
def RankRule (α : Type*) [MeasurableSpace α] :=
  {f : α → α → ({-1, 0, 1} : Set ℝ) // Measurable <| Function.uncurry f}
-- ANCHOR_END: RankRule

end RankRule

variable {α β : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] {n : ℕ}
  [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [LinearOrder β]
  [SecondCountableTopology β] [OpensMeasurableSpace β] [OrderClosedTopology β]
  (data : prod_iter_image α β n)

namespace RankOpt

/-- Computes the ranking from observed function values.
Returns 1 if `y₁ > y₂`, 0 if `y₁ = y₂`, and -1 if `y₁ < y₂`. -/
noncomputable def ranking_data (y₁ y₂ : β) := if y₂ < y₁ then 1 else if y₂ = y₁ then 0 else -1

/-- Indicator function checking if two rankings agree.
Returns 1 if both values are equal, 0 otherwise. -/
noncomputable abbrev rindicator (r₁ r₂ : ℝ) := if r₁ = r₂ then (1 : ℝ) else 0

/-- Computes the ranking loss for a rank rule.
Measures the agreement between a candidate rule `r` and the rankings induced by the observed
function values on all pairs of data points, normalized by the number of pairs. -/
noncomputable def ranking_loss (r : RankRule α) :=
  2 * (n * (n + 1) : ℝ)⁻¹ * ∑ ij ∈ {(i, j) : Iic n × Iic n | i ≤ j},
    rindicator (r.1 (data.1 ij.1) (data.1 ij.2)) (ranking_data (data.2 ij.1) (data.2 ij.2))

/-- The point in the observed data with the maximum function value. -/
noncomputable abbrev argmax_f := (data.1 <| Tuple.argmax (fun i ↦ data.2 i))

/-- The set of potential maximizers for the RankOpt algorithm.
Contains all points `x` for which there exists a ranking rule `r` in the hypothesis class `𝓡`
that: (1) has zero ranking loss (perfectly consistent with the observed data),
and (2) ranks `x` at least as high as the current best observed point. -/
def potential_max (𝓡 : Set (RankRule α)) :=
    {x | ∃ (r : 𝓡), ranking_loss data r = 0 ∧ 0 ≤ (r.1.1 x (argmax_f data)).1}

lemma measurableSet_potential_max_prod {𝓡 : Set (RankRule α)} (h𝓡 : 𝓡.Countable) :
    MeasurableSet {p : (prod_iter_image α β n) × α | p.2 ∈ potential_max p.1 𝓡} := by
  simp only [potential_max, Set.mem_setOf_eq, measurableSet_setOf]
  have : Countable (𝓡) := h𝓡.to_subtype
  refine Measurable.exists fun r ↦ (.and ?_ ?_)
  · simp only [ranking_loss]
    refine Measurable.eq ?_ measurable_const
    refine Measurable.const_mul (measurable_sum _ fun i hi ↦ ?_) _
    simp only [rindicator]
    refine Measurable.ite (measurableSet_eq_fun ?_ ?_) measurable_const measurable_const
    · have := r.1.2
      fun_prop
    · simp only [ranking_data]
      have : Measurable (fun (z : ℤ) ↦ (z : ℝ)) := by fun_prop
      refine this.comp ?_
      refine Measurable.ite ?_ measurable_const <| .ite ?_ measurable_const measurable_const
      · measurability
      · measurability
  · refine Measurable.le' measurable_const ?_
    have : Measurable (fun x : ({-1, 0, 1} : Set ℝ) ↦ (x : ℝ)) := by fun_prop
    refine this.comp (r.1.2.comp (measurable_snd.prodMk ?_))
    suffices Measurable (fun p : prod_iter_image α β n ↦ (p.1 <| Tuple.argmax (fun i ↦ p.2 i))) by
      exact this.comp measurable_fst
    have h_eval : Measurable (fun p : (prod_iter_image α β n) × Iic n ↦ p.1.1 p.2) := by
      refine measurable_from_prod_countable_left fun i ↦ ?_
      suffices Measurable (fun (x : iter α n) ↦ x i) from this.comp measurable_fst
      exact measurable_pi_apply i
    refine h_eval.comp (Measurable.prodMk (by fun_prop) ?_)
    change Measurable (fun p : prod_iter_image α β n ↦ Tuple.argmax (fun i ↦ (p.2 i)))
    fun_prop

end RankOpt

open RankOpt

/- We need that the set of potential maximizers has non-zero measure at each iteration,
ensuring that the algorithm can sample from it. -/
variable {𝓡 : Set (RankRule α)} (h𝓡 : 𝓡.Countable)
  (h : ∀ n (data : prod_iter_image α β n), μ (potential_max data 𝓡) ≠ 0)

/-- The RankOpt algorithm for global optimization.
This algorithm uses a ranking approach to optimize an unknown function. It maintains a hypothesis
class `𝓡` of ranking rules. It starts with an arbitrary probability measure `μ` as initial
distribution and samples from the set of points that could be optimal according to ranking rules
consistent with the observed data [(Malherbe et al., 2017)](https://arxiv.org/abs/1603.04381). -/
-- ANCHOR: RankOpt
noncomputable def RankOpt : Algorithm α β :=
  Decision μ (fun n ↦ measurableSet_potential_max_prod (n := n) h𝓡) h
-- ANCHOR_END: RankOpt
