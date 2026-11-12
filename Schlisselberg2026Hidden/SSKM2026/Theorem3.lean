/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent

/-!
# Theorem 3 of [SSKM26]: the smooth bound is tight

On `K = [0, D]` with the `β`-smooth regularizer `R x = β x² / 2`, the constant loss
`ℓ = min (√(2 β ε) / η, 1)` is so small that staying at the initial point `D / 2` is an
`ε`-approximate step at every round: the exact step improves the objective by
`η² ℓ² / (2 β) ≤ ε` only. Against `u = 0`, this trajectory has regret
`T D ℓ / 2 ≥ min (T D √(β ε) / η, D T) / 2`, which matches the upper bound of Theorem 2 of
[SSKM26] (`Schlisselberg2026Hidden.approxMirrorDescent_regret_le_of_smooth`).

## Main statements

* `Schlisselberg2026Hidden.exists_approxMirrorDescent_le_regret_euclidean`: [SSKM26, Theorem 3].

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore.OnlineLearning

namespace Schlisselberg2026Hidden

/-- **The smooth bound is tight** [SSKM26, Theorem 3]. For `β, ε, D, η > 0`, there are losses
`y t` on `ℝ` of dual norm at most `1`, an `ε`-approximate trajectory `a` of mirror descent on
`[0, D]` with the `β`-smooth regularizer `x ↦ β x² / 2` (whose derivative at `x` is `h ↦ β x h`)
and learning rate `η`, and a comparator `u ∈ [0, D]` such that for every horizon `T` the regret
is at least `min (T D √(β ε) / η, D T) / 2`.

The paper states the bound with `Ω(·)`; the constant `1 / 2` is that of its proof. The losses
and the trajectory do not depend on `T`. -/
theorem exists_approxMirrorDescent_le_regret_euclidean {β ε D η : ℝ} (hβ : 0 < β) (hε : 0 < ε)
    (hD : 0 < D) (hη : 0 < η) :
    ∃ y : ℕ → ℝ →L[ℝ] ℝ, (∀ t, ‖y t‖ ≤ 1) ∧ ∃ a : ℕ → ℝ, a 0 ∈ Set.Icc 0 D ∧
      (∀ t, IsApproxMirrorDescentStep (Set.Icc 0 D) (fun x ↦ β / 2 * x ^ 2) η (y t) (a t)
        ((β * a t) • ContinuousLinearMap.id ℝ ℝ) ε (a (t + 1))) ∧
      ∃ u ∈ Set.Icc 0 D, ∀ T : ℕ,
        min (T * D * √(β * ε) / η) (D * T) / 2 ≤ regret (fun t b ↦ y t b) a u T := by
  sorry

end Schlisselberg2026Hidden
