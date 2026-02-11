/-
 - Created in 2025 by Gaëtan Serré
-/

import Manual.Papers
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option pp.rawOnError true

set_option verso.exampleProject "../"

set_option verso.exampleModule "LeanGO.Doc.Algorithm"

#doc (Manual) "Abstract algorithm" =>
%%%
htmlSplit := .never
%%%

# Definition
A stochastic iterative global optimization algorithm can be seen as a stochastic process that iteratively samples from a search space, producing a sequence of samples. The first sample is drawn from a probability measure inherent to the algorithm, and subsequent samples are generated based on Markov kernels that depend on the previous samples and their associated evaluations by a measurable function. We define the following structure to represent such an algorithm.

```anchor Algorithm
structure Algorithm (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  ν : Measure α
  prob_measure : IsProbabilityMeasure ν
  kernel_iter (n : ℕ) : Kernel (prod_iter_image α β n) α
  markov_kernel (n : ℕ) : IsMarkovKernel (kernel_iter n)
```
The type {anchorTerm Algorithm}`prod_iter_image` is the product type `(Iic n → α) × (Iic n → β)` which represents the sequence of samples and their evaluations at each iteration. The measure {anchorTerm Algorithm}`ν` is the initial probability measure from which the first sample is drawn, and {anchorTerm Algorithm}`kernel_iter` is the Markov kernel that defines how to sample the next element based on the previous ones.

*To assess the validity of this definition, we encompass three well-known algorithms in the literature into this framework.*

## Pure Random Search
The Pure Random Search algorithm is a simple stochastic iterative global optimization algorithm that samples uniformly from the search space at each iteration. It can be defined as follows:
- {anchorTerm Algorithm}`ν` `:=` $`\mathcal{U}(\alpha)` is the uniform measure on the search space $`\alpha`.

- {anchorTerm Algorithm}`kernel_iter n` `:=` $`\_ \mapsto \mathcal{U}(\alpha)` is the Markov kernel that maps any pair of samples/evaluations to the uniform measure on $`\alpha`.

## AdaLIPO
The AdaLIPO algorithm has been introduced in {citep Malherbe2017}[] and is a more sophisticated stochastic iterative global optimization algorithm made for Lipschitz functions. It uses a estimation of the Lipschitz constant to adaptively sample the search space. The algorithm can be defined as follows:
- {anchorTerm Algorithm}`ν` `:=` $`\mathcal{U}(\alpha)` is the uniform measure on the search space $`\alpha`.

- {anchorTerm Algorithm}`kernel_iter n` `:=` $`(X, f(X)) \mapsto \mathcal{U}(E(X, f(X)))` is the Markov kernel that maps any pair of samples/evaluations to the uniform measure on the set $`E(X, f(X))` defined as
  $$`
  E(X, f(X)) \coloneqq \{x : \alpha \; | \; \max_{1 \le i \le n} f(X_i) \le \min_{1 \le i \le n} f(X_i) + \kappa(X, f(X)) \cdot d(x, X_i)\}
  `
  where $`(X, f(X)) \triangleq \left[(X_1, \dots, X_n), (f(X_1), \dots, f(X_n))\right]` and $`\kappa(X, f(X))` is an estimation of the Lipschitz constant of the function $`f` based on the previous samples and their evaluations.

### CMA-ES
The CMA-ES (Covariance Matrix Adaptation Evolution Strategy) is a well-known algorithm for continuous global optimization, introduced in {citep Hansen1996}[]. At each iteration, it samples $`k` points according to a multivariate normal distribution where the mean and the covariance matrix depend on the previous iterations. Given a continuous function $`f : \Omega \to \mathbb{R}`, we construct $`\tilde{f} : \Omega^k \to \mathbb{R}^k` by
$$`
  \tilde{f}(x_1, \dots, x_k) = (f(x_1), \dots, f(x_k)).
`
This new definition lets us view CMA-ES as a procedure that generates samples in $`\Omega^k`, where $`\tilde{f}` is employed to construct the transition kernels. The CMA-ES algorithm can be defined as follows:
- {anchorTerm Algorithm}`ν` `:=` $`\mathcal{N}^{\otimes k}(\mu, \Sigma)` is the $`k`-product of multivariate normal measures on the search space $`\alpha` with mean $`\mu` and covariance matrix $`\Sigma`.

- {anchorTerm Algorithm}`kernel_iter n` `:=` $`(X, \tilde{f}(X)) \mapsto \mathcal{N}(\mu(X, \tilde{f}(X)), \Sigma(X, \tilde{f}(X)))` is the Markov kernel that maps any pair of samples/evaluations to the multivariate normal distribution with mean $`\mu(X, \tilde{f}(X))` and covariance matrix $`\Sigma(X, \tilde{f}(X))` adapted based on the previous samples and their evaluations.

# Measure on sequences
To define the consistency of a stochastic iterative global optimization algorithm, we need to use the initial probability measure and the Markov kernels of an algorithm to construct a probability measure on infinite sequences of samples produced by the algorithm. We chose to use the Ionescu-Tulcea theorem {citep Tulcea1949}[] to define this measure. The implementation of this theorem in Mathlib is done via the {anchorTerm measure}`Kernel.traj` function, which, given a family of Markov kernels on finite sequences, returns a Markov kernel on infinite sequences.

To be able to use {anchorTerm measure}`Kernel.traj` with {anchorTerm Algorithm}`kernel_iter`, we need to pullback each kernel in the family along a function that, given a sequence of samples `u` and a continuous function `f`, returns `(u, f ∘ u)`. This new kernel is defined using {anchorTerm iter_comap}`iter_comap`.

```anchor iter_comap
def iter_comap (n : ℕ) : Kernel (iter α n) α :=
  (A.kernel_iter n).comap
    (prod_eval n f)
    (measurable_prod_eval n hf)
```

It allows to define a measure on sequences of size $`n + 1` by averaging the Ionescu-Tulcea kernel, given by {anchorTerm measure}`Kernel.traj (A.iter_comap hf) 0` over the initial measure `Algorithm.`{anchorTerm Algorithm}`ν` pulled back along the measurable equivalence between `Iic 0 → α` and `α`.

```anchor ν_mequiv
noncomputable def ν_mequiv : Measure (iter α 0) := A.ν.comap (MeasurableEquiv.funUnique _ _)
```

```anchor measure
noncomputable def measure (A : Algorithm α β) : Measure (ℕ → α) :=
  (Kernel.traj (A.iter_comap hf) 0).avg A.ν_mequiv
```

Because {anchorTerm Algorithm}`ν` is a probability measure, and all kernels {anchorTerm Algorithm}`kernel_iter` are Markov kernels, {anchorTerm measure}`measure` is a also probability measure on sequences of samples.
```anchor measure_isProbability
instance : IsProbabilityMeasure (A.measure hf) := by
  simp only [measure]
  infer_instance
```

Finally, we can define the measure on finite sequences of samples of size $`n + 1` produced by the algorithm by measuring set of infinite sequences of samples such that the first $`n + 1` elements are in a set of sequences of size $`n + 1`.

```anchor fin_measure
noncomputable def fin_measure {n : ℕ} : Measure (iter α n) := (A.measure hf).map (frestrictLe n)
```

# Useful properties
This definition of a stochastic iterative global optimization algorithm allows to prove two properties on the measure on sequences of samples. These theorems happen to be useful in our formalization.

## Monotone
The first theorem states that, given two natural integers such that $`n \le m`, a measurable set $`S` of sequences of size $`n + 1`, and a set $`E` of sequences of size $`m`, if the subsequences of size $`n` in $`E` are contained in $`S`, then the measure of $`E` is less than or equal to the measure of $`S`.

The informal intuition behind this theorem is that a sequence of size $`m` can be seen as a "continuations" of a sequence of size $`n + 1`. Thus, the hypothesis that the sequences of size $`m + 1` in $`E` are contained in the set of sequences of size $`m + 1` that are continuations of $`S` means that `$E` is a subset of all possible continuations of sequences in $`S`. Therefore, the measure of $`E` is less than or equal to the measure of $`S`.
```anchor mono
theorem fin_measure_mono {n m : ℕ} {s : Set (iter α n)} (hs : MeasurableSet s)
    {e : Set (iter α m)} (he : MeasurableSet e) (hmn : n ≤ m)
    (hse : e ⊆ {u | subTuple hmn u ∈ s}) {f : α → β} (hf : Measurable f) :
    A.fin_measure hf e ≤ A.fin_measure hf s := by
```
## Restricted measures
The second theorem states that, given two measurable functions $`f` and $`g` and a measurable set $`S` of elements of the search space $`\alpha` such that $`f` and $`g` are equal on $`S`, the measure on sequences produced by the algorithm using $`f` restricted to the set of sequences where all elements are in $`S` is equal to the same restricted measure using $`g`.

This is natural as the measures on sequences are entirely determined by the evaluations of the function on the samples.
```anchor eq_restrict
theorem eq_restrict {f g : α → β} (hf : Measurable f) (hg : Measurable g)
    {s : Set α} (hs : MeasurableSet s) (h : s.EqOn f g) (n : ℕ) :
    (A.fin_measure hf).restrict (univ.pi (fun (_ : Finset.Iic n) => s)) =
    (A.fin_measure hg).restrict (univ.pi (fun (_ : Finset.Iic n) => s)) := by
```
