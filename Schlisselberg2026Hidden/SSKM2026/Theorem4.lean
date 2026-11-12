/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent
public import LMLExplore.Analysis.Convex.NegEntropy

/-!
# Theorem 4 of [SSKM26]: the negative entropy needs exponentially small errors

On the simplex with at least two arms and the negative entropy, for every `η > 0` and every
`ε ≥ 4 η e^{-η T / 3}`, there are losses in `[0, 1]^d` and an `ε`-approximate trajectory of mirror
descent started at the uniform point whose regret against the best point in hindsight is at
least `T / 10`: errors that are not exponentially small in `η T` can cause linear regret.

For `η ≤ 1` this is Lemma 14 of [SSKM26] with `A = T / 3`, which gives `T / 6`. For `η > 1`,
exact mirror descent on alternating losses already has regret at least `T / 10`.

The paper states the regret as `Ω(T)` and proves it through Lemma 14 of [SSKM26], which is for two
arms and needs `η ≤ 1` (`notes/paper-errata.md`).

## Main statements

* `Schlisselberg2026Hidden.exists_approxMirrorDescent_le_regret_negEntropy`:
  [SSKM26, Theorem 4], with explicit constants.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α]

/-- **The negative entropy needs exponentially small errors** [SSKM26, Theorem 4], with explicit
constants. Let the simplex have at least two arms, `η > 0`, and `ε ≥ 4 η e^{-η T / 3}`. There are
losses in `[0, 1]^d`, an `ε`-approximate trajectory `a` of mirror descent on the simplex with the
negative entropy and learning rate `η`, started at the uniform point and with positive
coordinates, and a best point `u` of the simplex in hindsight, such that the regret of `a` against
`u` after `T` rounds is at least `T / 10`. -/
theorem exists_approxMirrorDescent_le_regret_negEntropy (h2 : 2 ≤ Fintype.card α) {η ε : ℝ}
    (hη : 0 < η) (T : ℕ) (hε : 4 * η * exp (-(η * T / 3)) ≤ ε) :
    ∃ ℓ : ℕ → α → ℝ, (∀ t i, ℓ t i ∈ Set.Icc 0 1) ∧
    ∃ a : ℕ → α → ℝ, a 0 = (fun _ ↦ (Fintype.card α : ℝ)⁻¹) ∧ (∀ t i, 0 < a t i) ∧
      (∀ t < T, IsApproxMirrorDescentStep (simplex α) negEntropy η
        (∑ i, ℓ t i • ContinuousLinearMap.proj i) (a t)
        (∑ i, log (a t i) • ContinuousLinearMap.proj i) ε (a (t + 1))) ∧
    ∃ u ∈ simplex α, (∀ v ∈ simplex α,
        ∑ t ∈ range T, ∑ i, ℓ t i * u i ≤ ∑ t ∈ range T, ∑ i, ℓ t i * v i) ∧
      (T : ℝ) / 10 ≤ regret (fun t w ↦ ∑ i, ℓ t i * w i) a u T := by
  sorry

end Schlisselberg2026Hidden
