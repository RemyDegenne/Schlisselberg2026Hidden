/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent
public import Schlisselberg2026Hidden.ForLMLExplore.Analysis.Convex.PowerBarrier
public import LMLExplore.Analysis.Convex.Simplex

/-!
# Theorem 35 of [SSKM26]: errors must be polynomially small in the dimension

For a power barrier `r` with exponent `ν` and lower constant `c₁` on the simplex with `d ≥ 2`
arms, if `η ≤ c₁ d^{ν-1} / (3 ν)` and `ε ≥ 4 η² / (c₁ d^ν)`, then for constant losses `1` on every
arm but one, staying at the uniform point is an `ε`-approximate step at every round, and the
regret is `T (1 - 1/d) ≥ T / 2`: the error must be polynomially small in `d`.

The steps are taken on the open simplex (positive coordinates), the domain of the barrier: in Lean
the value `r 0` is a junk value, which for the log barrier would make every positive step fail to
be approximate on the closed simplex.

The paper states the theorem with no condition on `η` (it is false for large `η`), without the
initial point, and with `Ω(T)`; its proof bounds the exact step with the curvature of `r` at the
wrong end of the step (`notes/paper-errata.md`).

## Main statements

* `Schlisselberg2026Hidden.exists_approxMirrorDescent_le_regret_of_isPowerBarrier`:
  [SSKM26, Theorem 35], corrected.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α]

/-- **Errors must be polynomially small in the dimension** [SSKM26, Theorem 35], corrected. Let
the simplex have `d ≥ 2` arms, let `r` be a power barrier with exponent `ν` and constants
`c₁, c₂`, and let `0 < η ≤ c₁ d^{ν-1} / (3 ν)` and `ε ≥ 4 η² / (c₁ d^ν)`. There are constant
losses `ℓ₀` in `[0, 1]^d`, an `ε`-approximate trajectory `a` of mirror descent on the open
simplex with potential `w ↦ ∑ i, r (w i)` and learning rate `η`, started at the uniform point,
and a best point `u` of the simplex in hindsight, such that for every horizon `T` the regret of
`a` against `u` is at least `T / 2`. -/
theorem exists_approxMirrorDescent_le_regret_of_isPowerBarrier (h2 : 2 ≤ Fintype.card α)
    {ν c₁ c₂ : ℝ} {r : ℝ → ℝ} (hr : IsPowerBarrier ν c₁ c₂ r) {η ε : ℝ} (hη : 0 < η)
    (hηd : η ≤ c₁ * (Fintype.card α : ℝ) ^ (ν - 1) / (3 * ν))
    (hε : 4 * η ^ 2 / (c₁ * (Fintype.card α : ℝ) ^ ν) ≤ ε) :
    ∃ ℓ₀ : α → ℝ, (∀ i, ℓ₀ i ∈ Set.Icc 0 1) ∧
    ∃ a : ℕ → α → ℝ, a 0 = (fun _ ↦ (Fintype.card α : ℝ)⁻¹) ∧
      (∀ t, IsApproxMirrorDescentStep {w | (∀ i, 0 < w i) ∧ ∑ i, w i = 1}
        (fun w ↦ ∑ i, r (w i)) η (∑ i, ℓ₀ i • ContinuousLinearMap.proj i) (a t)
        (∑ i, deriv r (a t i) • ContinuousLinearMap.proj i) ε (a (t + 1))) ∧
    ∃ u ∈ simplex α, (∀ v ∈ simplex α, ∑ i, ℓ₀ i * u i ≤ ∑ i, ℓ₀ i * v i) ∧
      ∀ T : ℕ, (T : ℝ) / 2 ≤ regret (fun _ w ↦ ∑ i, ℓ₀ i * w i) a u T := by
  sorry

end Schlisselberg2026Hidden
