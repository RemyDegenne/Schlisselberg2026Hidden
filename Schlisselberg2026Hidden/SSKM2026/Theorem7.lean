/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent
public import LMLExplore.Analysis.Convex.NegEntropy
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic

/-!
# Theorem 7 of [SSKM26]: stochastic losses make the negative entropy robust

On the simplex with the negative entropy, for i.i.d. losses in `[-1, 1]^d`, the uniform initial
point, `η = √(log d / T)` with `T ≥ 256 log d`, and `ε ≤ δ / (6 d³ T⁴)`, with probability at
least `1 - δ` every `ε`-approximate trajectory of mirror descent has regret at most
`2 √(T log d)`: polynomially small errors suffice, unlike for adversarial losses (Theorem 4 of
[SSKM26]).

With probability at least `1 - δ`, the i.i.d. losses are `√(2 T log (d² (T + 1)² / δ))`-balanced
(a sub-Gaussian bound for the bridges `L_{[s,t)}(i) - L_{[s,t)}(j) - (t - s)/T L_{[0,T)}(i) +
(t - s)/T L_{[0,T)}(j)`, which handles the random best arm), and Lemma 15 of [SSKM26] applies.

The paper states the theorem with `T ≥ 256`, `ε ≤ δ / (6 d² T⁴)` and `O(√(T log d))`; its proof
needs `η ≤ 1/16`, that is `T ≥ 256 log d`, and does not give the factor `d²`
(`notes/paper-errata.md`).

## Main statements

* `Schlisselberg2026Hidden.approxMirrorDescent_regret_le_negEntropy_iid`: [SSKM26, Theorem 7],
  corrected.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real MeasureTheory ProbabilityTheory

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α] {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Stochastic losses make the negative entropy robust** [SSKM26, Theorem 7], with corrected
constants. Let the losses `ℓ t` be independent and identically distributed over the rounds, with
coordinates in `[-1, 1]`, let `0 < δ ≤ 1`, `T ≥ 256 log d` with `d` the number of arms, and
`ε ≤ δ / (6 d³ T⁴)`. Then there is a measurable event of probability at least `1 - δ` on which
every `ε`-approximate trajectory `a` of mirror descent on the simplex with the negative entropy
and learning rate `√(log d / T)`, started at the uniform point and with positive coordinates, has
regret at most `2 √(T log d)` against every point of the simplex. -/
theorem approxMirrorDescent_regret_le_negEntropy_iid {P : Measure Ω} [IsProbabilityMeasure P]
    (ℓ : ℕ → Ω → α → ℝ) (hℓ_meas : ∀ t, Measurable (ℓ t)) (hℓ_indep : iIndepFun ℓ P)
    (hℓ_ident : ∀ t, IdentDistrib (ℓ t) (ℓ 0) P P) (hℓ : ∀ t ω i, ℓ t ω i ∈ Set.Icc (-1) 1)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {T : ℕ} (hT : 256 * log (Fintype.card α) ≤ T)
    (hε : ε ≤ δ / (6 * (Fintype.card α : ℝ) ^ 3 * (T : ℝ) ^ 4)) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - δ ≤ P.real E ∧ ∀ ω ∈ E, ∀ a : ℕ → α → ℝ,
      a 0 = (fun _ ↦ (Fintype.card α : ℝ)⁻¹) → (∀ t ≤ T, ∀ i, 0 < a t i) →
      (∀ t < T, IsApproxMirrorDescentStep (simplex α) negEntropy √(log (Fintype.card α) / T)
        (∑ i, ℓ t ω i • ContinuousLinearMap.proj i) (a t)
        (∑ i, log (a t i) • ContinuousLinearMap.proj i) ε (a (t + 1))) →
      ∀ u ∈ simplex α, regret (fun t w ↦ ∑ i, ℓ t ω i * w i) a u T ≤
        2 * √(T * log (Fintype.card α)) := by
  sorry

end Schlisselberg2026Hidden
