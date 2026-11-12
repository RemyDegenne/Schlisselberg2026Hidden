/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent
public import LMLExplore.Analysis.Convex.NegEntropy

/-!
# Theorem 36 of [SSKM26]: linear regret although the exact trajectory stays away from zero

On the simplex with two arms `i₁, i₂` and the negative entropy, let `0 < η ≤ 1` and
`40 τ ≤ T`. The losses put loss `1` on `i₂` for `3 τ` rounds, on `i₁` for `2 τ` rounds, then on
`i₂` again; `i₁` is the best arm and the losses are `2 τ`-balanced. The exact trajectory keeps
weight at least `1/2` on `i₁`, but for every `ε ≥ 4 η e^{-η τ}` an `ε`-approximate trajectory
gets stuck twice, first while `i₂` is good and then, after `i₁` has been pushed down by the second
phase, while `i₁` is good, and has regret at least `T / 3`.

The paper states the theorem with `k ≤ T η / 20` and `ε = 4 η e^{-k/2}` (so `τ = k / (2 η)`, which
it does not require to be an integer), `Ω(T)`, and no condition on `η`; the construction needs
`η ≤ 1` (`notes/paper-errata.md`).

## Main statements

* `Schlisselberg2026Hidden.exists_approxMirrorDescent_le_regret_negEntropy_threePhase`:
  [SSKM26, Theorem 36], corrected.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Linear regret although the exact trajectory stays away from zero** [SSKM26, Theorem 36],
corrected. Let the simplex have two arms `i₁ ≠ i₂`, let `0 < η ≤ 1` and `40 τ ≤ T`. There are
losses in `[0, 1]²` for which `i₁` is a best arm over `T` rounds and which are `2 τ`-balanced with
respect to `i₁`, such that every exact trajectory of mirror descent on the simplex with the
negative entropy and learning rate `η`, started at the uniform point, keeps weight at least `1/2`
on `i₁`, and a trajectory `a` started at the uniform point with positive coordinates which is an
`ε`-approximate trajectory for every `ε ≥ 4 η e^{-η τ}` and has regret at least `T / 3` against
the vertex `i₁`. -/
theorem exists_approxMirrorDescent_le_regret_negEntropy_threePhase (h2 : Fintype.card α = 2)
    {i₁ i₂ : α} (h12 : i₁ ≠ i₂) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {τ T : ℕ}
    (hτT : 40 * τ ≤ T) :
    ∃ ℓ : ℕ → α → ℝ, (∀ t i, ℓ t i ∈ Set.Icc 0 1) ∧
      (∀ i, ∑ t ∈ range T, ℓ t i₁ ≤ ∑ t ∈ range T, ℓ t i) ∧
      (∀ s t, s ≤ t → t ≤ T → ∀ i, ∑ r ∈ Ico s t, (ℓ r i₁ - ℓ r i) ≤ 2 * τ) ∧
      (∀ b : ℕ → α → ℝ, b 0 = (fun _ ↦ (Fintype.card α : ℝ)⁻¹) → (∀ t ≤ T, ∀ i, 0 < b t i) →
        (∀ t < T, IsMirrorDescentStep (simplex α) negEntropy η
          (∑ i, ℓ t i • ContinuousLinearMap.proj i) (b t)
          (∑ i, log (b t i) • ContinuousLinearMap.proj i) (b (t + 1))) →
        ∀ t ≤ T, 1 / 2 ≤ b t i₁) ∧
    ∃ a : ℕ → α → ℝ, a 0 = (fun _ ↦ (Fintype.card α : ℝ)⁻¹) ∧ (∀ t i, 0 < a t i) ∧
      (∀ ε, 4 * η * exp (-(η * τ)) ≤ ε → ∀ t < T,
        IsApproxMirrorDescentStep (simplex α) negEntropy η
          (∑ i, ℓ t i • ContinuousLinearMap.proj i) (a t)
          (∑ i, log (a t i) • ContinuousLinearMap.proj i) ε (a (t + 1))) ∧
      (T : ℝ) / 3 ≤ regret (fun t w ↦ ∑ i, ℓ t i * w i) a (Pi.single i₁ 1) T := by
  sorry

end Schlisselberg2026Hidden
