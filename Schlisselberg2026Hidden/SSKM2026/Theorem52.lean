/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.FTRL.Approx

/-!
# Theorem 52 of [SSKM26]: approximate follow the regularized leader

For follow the regularized leader, the objective of each round is the cumulative loss plus the
regularizer, which does not depend on the previous plays: approximation errors do not compound.
With a `1`-strongly convex regularizer `R` on a compact convex set, losses of dual norm at most `1`,
an exact first play and `ε`-approximate plays afterwards, the regret against every `u ∈ K` is at
most `(R u - R (a 0)) / η + (2 η + √(2 ε)) T`.

The proof compares each approximate play `a t` with the exact play `x (t + 1)` of the next
round, `‖a t - x (t + 1)‖ ≤ 2 η + √(2 ε)` [SSKM26, Lemma 51], and uses the "be the leader"
inequality for the exact plays [SSKM26, Lemma 50].

## Main statements

* `Schlisselberg2026Hidden.approxFTRL_regret_le`: [SSKM26, Theorem 52].

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore.OnlineLearning

namespace Schlisselberg2026Hidden

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Approximate follow the regularized leader** [SSKM26, Theorem 52]. Let `K` be a compact
convex set and let `R` have a derivative `R' x` within `K` at every `x ∈ K` and be `1`-strongly
convex on `K`. Let `η > 0` and let the losses `y t`, `t < T`, have dual norm at most `1`. If
`a 0` is the first play of FTRL (a minimizer of `R` over `K`) and each `a t`, `t < T`, is an
`ε`-approximate play of FTRL on `K` at round `t` with potential `R` and learning rate `η`, then for
every `u ∈ K` the regret after `T` rounds is at most `(R u - R (a 0)) / η + (2 η + √(2 ε)) T`.

The paper states this for a bounded closed convex set `K ⊆ ℝ^d`. -/
theorem approxFTRL_regret_le {K : Set E} (hK : Convex ℝ K) (hKc : IsCompact K) {R : E → ℝ}
    (R' : E → E →L[ℝ] ℝ) (hR' : ∀ x ∈ K, HasFDerivWithinAt R (R' x) K x)
    (hR : StrongConvexOn K 1 R) {η ε : ℝ} (hη : 0 < η) {T : ℕ} (y : ℕ → E →L[ℝ] ℝ)
    (hy : ∀ t < T, ‖y t‖ ≤ 1) (a : ℕ → E) (ha0 : IsFTRLPlay K R η y 0 (a 0))
    (ha : ∀ t < T, IsApproxFTRLPlay K R η y t ε (a t)) {u : E} (hu : u ∈ K) :
    regret (fun t b ↦ y t b) a u T ≤ (R u - R (a 0)) / η + (2 * η + √(2 * ε)) * T := by
  sorry

end Schlisselberg2026Hidden
