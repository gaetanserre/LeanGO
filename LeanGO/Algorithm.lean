/-
 - Created in 2025 by Gaëtan Serré
-/

import LeanGO.Utils.Kernel
import LeanGO.Utils.Measure
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

open MeasureTheory ProbabilityTheory

/-- `Algorithm α β` represents a general iterative stochastic optimization algorithm.

It models a sequence of updates where:
- `α` is the search space (e.g., parameters, candidate solutions),
- `β` is the evaluation space (e.g., objective values, feedback),
- `ν` is the initial probability measure over `α` (the starting distribution of candidates),
- `kernel_iter n` is a Markov kernel that outputs a new candidate in `α`
  given the history of the first `n` points and their evaluations,
  i.e., from the space `prod_iter_image α β n` = (`α × β`)ⁿ,
- `markov_kernel n` asserts that each such `kernel_iter n` is a valid Markov kernel.

It allows formal reasoning over joint distributions of evaluated points and convergence
properties. -/
structure Algorithm (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  ν : Measure α
  prob_measure : IsProbabilityMeasure ν
  kernel_iter (n : ℕ) : Kernel (prod_iter_image α β n) α
  markov_kernel (n : ℕ) : IsMarkovKernel (kernel_iter n)

namespace Algorithm

open Tuple ENNReal Set

variable {α β : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
  [MeasurableSpace β] [TopologicalSpace β] [BorelSpace β] (A : Algorithm α β)

instance : IsProbabilityMeasure (A.ν) := A.prob_measure

instance {n : ℕ} : IsMarkovKernel (A.kernel_iter n) := A.markov_kernel n

/- To be able to construct a measure on infinite sequences of iterations, we need
to pullback `μ` along a measurable equivalence that will change the type of `ν` from
`Measure α` to `Measure iter α 0`. -/

/-- The finite type `Finset.Iic 0` is a singleton type, which only contains the element `0`. -/
instance : Unique (Finset.Iic 0) where
  default := ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 0)⟩
  uniq a := by
    refine Subtype.coe_eq_of_eq_mk ?_
    by_contra h
    have := Finset.mem_Iic.mp a.2
    omega

/-- The measure `ν` that has been pulled back along the measurable equivalence
`MeasurableEquiv.funUnique (iter α 0) α` to change the type of `ν` from
`Measure α` to `Measure (iter α 0)`. -/
noncomputable def ν_mequiv : Measure (iter α 0) := A.ν.comap (MeasurableEquiv.funUnique _ _)

instance : IsProbabilityMeasure (A.ν_mequiv) := by
  simp only [ν_mequiv]
  rw [isProbabilityMeasure_iff]
  rw [Measure.comap_apply _ (MeasurableEquiv.funUnique _ _).injective]
  · simp only [MeasurableEquiv.funUnique_apply, image_univ]
    suffices range (fun (a : iter α 0) => a default) = univ by
      rw [this]
      simp only [measure_univ]
    ext x
    constructor
    · intro _
      trivial
    · intro hx
      simp only [mem_range]
      exact ⟨fun i => x, rfl⟩
  · intro s hs
    exact ((MeasurableEquiv.funUnique _ _).measurableSet_image).mpr hs
  · exact MeasurableSet.univ

variable {f : α → β} (hf : Continuous f)

/-- Given a continuous function `f : α → β` representing the evaluation (e.g., objective function),
this constructs a new kernel that maps a history of points (in `iter α n`)
to a probability distribution over the next point in `α`.

The original algorithm `A` provides a transition kernel `A.kernel_iter n` that depends on
both the previously proposed points and their corresponding evaluations.
However, in practice, the algorithm itself only generates the sequence of points,
and the evaluations are computed externally by applying `f` to each point.

The function `prod_eval n f` deterministically reconstructs the full history
(points and their evaluations) from the point sequence alone, using `f` and
the `comap` pulls back the original kernel along this map,
resulting in a kernel that operates directly on the sequence of points. -/
def iter_comap (n : ℕ) : Kernel (iter α n) α :=
  (A.kernel_iter n).comap
    (prod_eval n f)
    (measurable_prod_eval n hf.measurable)

instance : ∀ n, IsMarkovKernel (A.iter_comap (n := n) hf) := by
  simp only [iter_comap]
  infer_instance

/-- The measure on infinite sequences of iterations. It is constructed by first obtaining
a kernel from `iter α 0` to `ℕ → α` via the Ionescu-Tulcea theorem, and then averaging the kernel
over the initial measure `A.ν_mequiv`. This gives a measure on the space of infinite sequences
of points in `α`, which can be used to analyze the convergence properties of the algorithm. -/
noncomputable def measure (A : Algorithm α β) : Measure (ℕ → α) :=
  (Kernel.traj (A.iter_comap hf) 0).avg A.ν_mequiv

instance : IsProbabilityMeasure (A.measure hf) := by
  simp only [measure]
  infer_instance

open Preorder

/-- The measure on finite sequences of iterations, defined by pushing forward `measure`
along the measurable function `frestrictLe n : (ℕ → α) → iter α n` that restricts
the infinite sequence to its first `n` elements. This is the measure that will be used
throughout the formalization. -/
noncomputable def fin_measure {n : ℕ} : Measure (iter α n) := (A.measure hf).map (frestrictLe n)

/-- The finite measure `A.fin_measure hf` can be expressed as the average of the
partial trajectory kernel from `0` to `n`, averaged over the initial measure `A.ν_mequiv`. -/
lemma fin_measure_eq_partial_traj {n : ℕ} : A.fin_measure hf =
    (Kernel.partialTraj (X := fun _ ↦ α) (A.iter_comap hf) 0 n).avg A.ν_mequiv := by
  simp only [fin_measure, measure]
  ext s hs
  rw [Measure.map_apply (measurable_frestrictLe n) hs, Kernel.avg_apply _ _ hs,
    Kernel.avg_apply _ _ (measurable_frestrictLe n hs)]
  congr with _
  rw [← Kernel.traj_map_frestrictLe, Kernel.map_apply' _ (measurable_frestrictLe n) _ hs]

instance {n : ℕ} : IsProbabilityMeasure (A.fin_measure hf (n := n)) := by
  simp only [fin_measure_eq_partial_traj]
  infer_instance

/-- Monotonicity of the algorithm's induced measures under trajectory extension.

Let `s : Set iter α n` be a measurable set of point sequences of length `n`,
and `e : Set iter α m` for some `m ≥ n` a set of longer trajectories such that
every `u ∈ e` satisfies `subTuple hmn u ∈ s`.

Then the measure assigned to `e` by the algorithm at step `m` is less than or equal to
the measure assigned to `s` at step `n`.

This expresses that the family of measures is projectively consistent:
the measure on longer trajectories contracts to the measure on shorter ones via truncation.

Formally: if `e ⊆ {u | subTuple hmn u ∈ s}`, then `A.fin_measure hf m e ≤ A.fin_measure hf n s`. -/
theorem fin_measure_mono {n m : ℕ} {s : Set (iter α n)} (hs : MeasurableSet s)
    {e : Set (iter α m)} (he : MeasurableSet e) (hmn : n ≤ m)
    (hse : e ⊆ {u | subTuple hmn u ∈ s}) {f : α → β} (hf : Continuous f) :
    A.fin_measure hf e ≤ A.fin_measure hf s := by
  simp only [fin_measure_eq_partial_traj, ← Kernel.traj_map_frestrictLe]
  rw [Kernel.avg_apply _ _ he]
  rw [Kernel.avg_apply _ _ hs]
  set κ := (Kernel.traj (X := fun _ => α) (A.iter_comap hf) 0)
  have : ∀ a, κ.map (frestrictLe n) a s = (κ a) ((frestrictLe n) ⁻¹' s) := by
    intro a
    exact Kernel.map_apply' κ (measurable_frestrictLe n) a hs
  simp_rw [this]
  clear this
  have : ∀ a, κ.map (frestrictLe m) a e = (κ a) ((frestrictLe m) ⁻¹' e) := by
    intro a
    exact Kernel.map_apply' κ (measurable_frestrictLe m) a he
  simp_rw [this]
  clear this
  simp only [preimage, ge_iff_le]
  suffices {x : ℕ → α | frestrictLe m x ∈ e} ⊆ {x | frestrictLe n x ∈ s} from
    lintegral_mono (fun a => (κ a).mono this)
  intro x hx
  simp_all only [mem_setOf_eq]
  exact hse hx

/-- If two continuous functions `f` and `g` agree on a measurable set `s`, then the algorithm's
induced measures at iteration `n` are identical when restricted to trajectories that stay
within `s`. This establishes that the algorithm depends only on the objective function values
on the relevant domain. -/
theorem eq_restrict {f g : α → β} (hf : Continuous f) (hg : Continuous g)
    {s : Set α} (hs : MeasurableSet s) (h : s.EqOn f g) (n : ℕ) :
    (A.fin_measure hf).restrict (univ.pi (fun (_ : Finset.Iic n) => s)) =
    (A.fin_measure hg).restrict (univ.pi (fun (_ : Finset.Iic n) => s)) := by
  refine Measure.pi_space_eq ?_
  intro B B_m
  let C := fun i => (B i) ∩ s
  set E := univ.pi (fun (i : Finset.Iic 0) => C ⟨i, mem_iic_le (Nat.zero_le n) i.2⟩)
  have eq_on_partialTraj : E.EqOn
      (fun a => Kernel.partialTraj (X := fun _ => α) (A.iter_comap hf) 0 n a (univ.pi C))
      (fun a => Kernel.partialTraj (X := fun _ => α) (A.iter_comap hg) 0 n a (univ.pi C)) := by
    suffices E.EqOn
        (fun a => (Kernel.partialTraj (X := fun _ => α) (A.iter_comap hf) 0 n a).restrict
        (univ.pi C))
        (fun a => (Kernel.partialTraj (X := fun _ => α) (A.iter_comap hg) 0 n a).restrict
        (univ.pi C)) by
      intro a a_mem
      specialize this a_mem
      simp_all only
      rw [← Measure.restrict_eq_self _ (subset_refl _)]
      nth_rw 2 [← Measure.restrict_eq_self _ (subset_refl _)]
      rw [this]
    let C_n : ℕ → Set α := fun i =>
      if h : i ≤ n then
        C ⟨i, Finset.mem_Iic.mpr h⟩
      else
        C ⟨0, Finset.mem_Iic.mpr (by omega)⟩
    have : (univ.pi C) = univ.pi (fun i => C_n i.1) := by
      simp_all only [Subtype.forall, Finset.mem_Iic, C_n, C]
      ext
      simp_all only [mem_pi, mem_univ, mem_inter_iff, forall_const, Subtype.forall, Finset.mem_Iic,
       ↓reduceDIte, mem_inter_iff]
    rw [this]
    clear this
    have : E = univ.pi (fun i => C_n i.1) := by
      simp_all only [Subtype.forall, Finset.mem_Iic, C_n, C, E]
      ext
      simp_all only [mem_pi, mem_univ, mem_inter_iff, forall_const, Subtype.forall, Finset.mem_Iic,
        nonpos_iff_eq_zero, zero_le, ↓reduceDIte]
    rw [this]
    clear this
    apply Kernel.partialTraj_restrict' (by omega)
    · intro i
      by_cases h : i ≤ n
      · simp only [h, ↓reduceDIte, C_n]
        exact (B_m ⟨i, Finset.mem_Iic.mpr h⟩).inter hs
      · simp only [h, ↓reduceDIte, C_n]
        exact (B_m ⟨0, Finset.mem_Iic.mpr (by omega)⟩).inter hs
    · intro m a a_mem
      simp only [iter_comap, Kernel.coe_comap, Function.comp_apply]
      suffices ∀ i, a i ∈ s by
        rw [prod_eval_eq_restrict m h this]
      intro i
      have := (a_mem i trivial)
      by_cases h : i ≤ n
      all_goals simp only [h, ↓reduceDIte, C_n] at this; exact this.2
  simp only [Measure.restrict_apply (MeasurableSet.univ_pi B_m)]
  have pi_inter : univ.pi B ∩ (univ.pi (fun _ => s)) = univ.pi C := pi_inter_distrib.symm
  rw [pi_inter]
  clear pi_inter
  simp only [fin_measure_eq_partial_traj]
  rw [Kernel.partialTraj_avg_rect_eq _ (Nat.zero_le n) _ (fun i ↦ (B_m i).inter hs)]
  rw [Kernel.partialTraj_avg_rect_eq _ (Nat.zero_le n) _ (fun i ↦ (B_m i).inter hs)]
  rw [setLIntegral_congr_fun ?_ eq_on_partialTraj]
  exact MeasurableSet.univ_pi (fun i => (B_m ⟨i, mem_iic_le (Nat.zero_le n) i.2⟩).inter hs)

end Algorithm
