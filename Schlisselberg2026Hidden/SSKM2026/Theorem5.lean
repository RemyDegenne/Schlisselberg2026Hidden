/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent
public import LMLExplore.Analysis.Convex.NegEntropy

/-!
# Theorem 5 of [SSKM26]: exponentially small errors suffice for the negative entropy

On the simplex with the negative entropy, for losses in `[0, 1]^d`, `η ≤ 1/16`, the uniform initial
point and `ε ≤ e^{-η T / 2} min (η⁴, 1/T²) / (100 d)`, every `ε`-approximate trajectory of mirror
descent has regret at most `log d / η + η T`. Together with Theorem 4 of [SSKM26], which gives
linear regret for `ε ≥ 4 η e^{-η T / 3}`, this shows that the negative entropy tolerates only
exponentially small errors.

Losses in `[0, 1]^d` are `T / 2`-balanced, so this is Lemma 15 of [SSKM26] with `A = T / 2`.

The paper states the theorem for losses in `[-1, 1]^d`, where it is false; with the threshold
`e^{-η T / 2} min (η⁴, T^{-2}) / (6 d)`, the comparator term `D_R(w, w₁) / η`, `O(η T)`, `T ≥ 3`
and no initial point (`notes/paper-errata.md`).

## Main statements

* `Schlisselberg2026Hidden.approxMirrorDescent_regret_le_negEntropy`: [SSKM26, Theorem 5],
  corrected.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α]

/-- **Exponentially small errors suffice for the negative entropy** [SSKM26, Theorem 5], for
losses in `[0, 1]^d` and with corrected constants. Let `0 < η ≤ 1/16`, let the losses `ℓ t` have
coordinates in `[0, 1]`, and let `ε ≤ e^{-η T / 2} min (η⁴, 1/T²) / (100 d)`, with `d` the number
of arms. Then every `ε`-approximate trajectory `a` of mirror descent on the simplex with the
negative entropy and learning rate `η`, started at the uniform point and with positive
coordinates, has regret at most `log d / η + η T` against every point of the simplex. -/
theorem approxMirrorDescent_regret_le_negEntropy {η ε : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 16)
    {T : ℕ} (ℓ : ℕ → α → ℝ) (hℓ : ∀ t < T, ∀ i, ℓ t i ∈ Set.Icc 0 1)
    (hε : ε ≤ exp (-(η * T / 2)) * min (η ^ 4) (1 / (T : ℝ) ^ 2) / (100 * Fintype.card α))
    (a : ℕ → α → ℝ) (ha0 : a 0 = fun _ ↦ (Fintype.card α : ℝ)⁻¹)
    (hpos : ∀ t ≤ T, ∀ i, 0 < a t i)
    (ha : ∀ t < T, IsApproxMirrorDescentStep (simplex α) negEntropy η
      (∑ i, ℓ t i • ContinuousLinearMap.proj i) (a t)
      (∑ i, log (a t i) • ContinuousLinearMap.proj i) ε (a (t + 1)))
    {u : α → ℝ} (hu : u ∈ simplex α) :
    regret (fun t w ↦ ∑ i, ℓ t i * w i) a u T ≤ log (Fintype.card α) / η + η * T := by
  sorry

end Schlisselberg2026Hidden
