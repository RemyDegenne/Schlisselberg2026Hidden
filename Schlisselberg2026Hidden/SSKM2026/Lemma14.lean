/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent
public import LMLExplore.Analysis.Convex.NegEntropy

/-!
# Lemma 14 of [SSKM26]: balanced losses with linear regret for the negative entropy

On the simplex with at least two arms and the negative entropy, for `0 < η ≤ 1` and
`0 ≤ A ≤ T / 2`, there are `A`-balanced losses in `[0, 1]^d` and a trajectory started at the
uniform point that is `ε`-approximate for every `ε ≥ 4 η e^{-η A}` and has regret at least
`(T - 2 A) / 2` against the best arm `i₁`. The losses put loss `1` on `i₁` for `⌊A⌋` rounds, so
that its weight under exact steps falls to about `e^{-η A}`, and then loss `1` on all the other
arms; from then on, staying put is an `ε`-approximate step.

The paper states the lemma for two arms, chooses the losses after `ε` in its proof, gives the
regret `Ω(T - 2α)` (its accounting gives `(T - 3τ) / 2`), and has no condition on `η`; the
construction needs `η ≤ 1` (`notes/paper-errata.md`).

## Main statements

* `Schlisselberg2026Hidden.exists_approxMirrorDescent_le_regret_of_balanced`:
  [SSKM26, Lemma 14], corrected.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Balanced losses with linear regret** [SSKM26, Lemma 14], corrected. Let the simplex have at
least two arms, let `i₁` be an arm, `0 < η ≤ 1`, and `0 ≤ A` with `2 A ≤ T`. There are losses in
`[0, 1]^d` for which `i₁` is a best arm over `T` rounds and which are `A`-balanced with respect to
`i₁`, and a trajectory `a` started at the uniform point with positive coordinates, such that for
every `ε ≥ 4 η e^{-η A}`, `a` is an `ε`-approximate trajectory of mirror descent on the simplex with
the negative entropy and learning rate `η`, and its regret against the vertex `i₁` is at least
`(T - 2 A) / 2`. The losses and the trajectory do not depend on `ε`. -/
theorem exists_approxMirrorDescent_le_regret_of_balanced (h2 : 2 ≤ Fintype.card α) (i₁ : α)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (T : ℕ) {A : ℝ} (hA : 0 ≤ A) (hAT : 2 * A ≤ T) :
    ∃ ℓ : ℕ → α → ℝ, (∀ t i, ℓ t i ∈ Set.Icc 0 1) ∧
      (∀ i, ∑ t ∈ range T, ℓ t i₁ ≤ ∑ t ∈ range T, ℓ t i) ∧
      (∀ s t, s ≤ t → t ≤ T → ∀ i, ∑ r ∈ Ico s t, (ℓ r i₁ - ℓ r i) ≤ A) ∧
    ∃ a : ℕ → α → ℝ, a 0 = (fun _ ↦ (Fintype.card α : ℝ)⁻¹) ∧ (∀ t i, 0 < a t i) ∧
      (∀ ε, 4 * η * exp (-(η * A)) ≤ ε → ∀ t < T,
        IsApproxMirrorDescentStep (simplex α) negEntropy η
          (∑ i, ℓ t i • ContinuousLinearMap.proj i) (a t)
          (∑ i, log (a t i) • ContinuousLinearMap.proj i) ε (a (t + 1))) ∧
      (T - 2 * A) / 2 ≤ regret (fun t w ↦ ∑ i, ℓ t i * w i) a (Pi.single i₁ 1) T := by
  sorry

end Schlisselberg2026Hidden
