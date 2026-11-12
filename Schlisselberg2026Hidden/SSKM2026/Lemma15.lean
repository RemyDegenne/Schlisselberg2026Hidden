/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent
public import LMLExplore.Analysis.Convex.NegEntropy

/-!
# Lemma 15 of [SSKM26]: balanced losses and the negative entropy

On the simplex, with the negative entropy, a loss sequence is `A`-balanced if on every interval of
rounds the cumulative loss of a best arm `i*` exceeds that of any other arm by at most `A`. For
such losses in `[-1, 1]^d`, `η ≤ 1/16`, the uniform initial point and
`ε ≤ e^{-η A} min (η⁴, 1/T²) / (100 d)`, every `ε`-approximate trajectory of mirror descent has
regret at most `log d / η + η T` against every point of the simplex.

The proof shows that the weight of `i*` stays at least `e^{-(η A + 1)} / d` along the trajectory
(the paper's Lemma 40, with corrected constants), and then runs the analysis of mirror descent
against the vertex `e_{i*}` only, where the approximate first-order condition of each step costs
`η² / 2`.

The paper's Lemma 15 has the threshold `min (η⁴, 1/T²) / (d max (6 e^{η α}, 1/η))`, the bound
`D_R(w, w₁) / η + O(η T)` for every `w`, `T ≥ 3`, and no initial point; its proof gives
neither the constant `6` nor the comparator term for `w ≠ e_{i*}`, and needs the uniform initial
point (`notes/paper-errata.md`).

## Main statements

* `Schlisselberg2026Hidden.approxMirrorDescent_regret_le_negEntropy_of_balanced`:
  [SSKM26, Lemma 15], corrected.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α]

/-- **Balanced losses and the negative entropy** [SSKM26, Lemma 15], with corrected constants.
Let `0 < η ≤ 1/16`, let the losses `ℓ t` have coordinates in `[-1, 1]`, let `i*` be a best arm
over the `T` rounds, and let the losses be `A`-balanced: `L_{[s, t)}(i*) - L_{[s, t)}(i) ≤ A` for
all `s ≤ t ≤ T` and all arms `i`. Let `ε ≤ e^{-η A} min (η⁴, 1/T²) / (100 d)`, with `d` the number
of arms. Then every `ε`-approximate trajectory `a` of mirror descent on the simplex with the
negative entropy and learning rate `η`, started at the uniform point and with positive
coordinates, has regret at most `log d / η + η T` against every point of the simplex. -/
theorem approxMirrorDescent_regret_le_negEntropy_of_balanced {η ε A : ℝ} (hη : 0 < η)
    (hη' : η ≤ 1 / 16) {T : ℕ} (ℓ : ℕ → α → ℝ) (hℓ : ∀ t < T, ∀ i, |ℓ t i| ≤ 1) (iStar : α)
    (hbest : ∀ i, ∑ t ∈ range T, ℓ t iStar ≤ ∑ t ∈ range T, ℓ t i)
    (hbal : ∀ s t, s ≤ t → t ≤ T → ∀ i, ∑ r ∈ Ico s t, (ℓ r iStar - ℓ r i) ≤ A)
    (hε : ε ≤ exp (-(η * A)) * min (η ^ 4) (1 / (T : ℝ) ^ 2) / (100 * Fintype.card α))
    (a : ℕ → α → ℝ) (ha0 : a 0 = fun _ ↦ (Fintype.card α : ℝ)⁻¹)
    (hpos : ∀ t ≤ T, ∀ i, 0 < a t i)
    (ha : ∀ t < T, IsApproxMirrorDescentStep (simplex α) negEntropy η
      (∑ i, ℓ t i • ContinuousLinearMap.proj i) (a t)
      (∑ i, log (a t i) • ContinuousLinearMap.proj i) ε (a (t + 1)))
    {u : α → ℝ} (hu : u ∈ simplex α) :
    regret (fun t w ↦ ∑ i, ℓ t i * w i) a u T ≤ log (Fintype.card α) / η + η * T := by
  sorry

end Schlisselberg2026Hidden
