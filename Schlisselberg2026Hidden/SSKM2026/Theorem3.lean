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
  -- the constant loss `ℓ = min (√(2 β ε) / η) 1`, the constant trajectory `D / 2`, and `u = 0`
  set ℓ := min (√(2 * β * ε) / η) 1 with hℓ
  have hℓ0 : 0 ≤ ℓ := le_min (by positivity) zero_le_one
  have hηℓ : η * ℓ ≤ √(2 * β * ε) := by
    calc η * ℓ ≤ η * (√(2 * β * ε) / η) := mul_le_mul_of_nonneg_left (min_le_left _ _) hη.le
    _ = √(2 * β * ε) := mul_div_cancel₀ _ hη.ne'
  have hηℓ2 : (η * ℓ) ^ 2 ≤ 2 * β * ε := by
    have := pow_le_pow_left₀ (by positivity) hηℓ 2
    rwa [Real.sq_sqrt (by positivity)] at this
  refine ⟨fun _ ↦ ℓ • ContinuousLinearMap.id ℝ ℝ, fun t ↦ ?_, fun _ ↦ D / 2,
    ⟨by positivity, by linarith⟩, fun t ↦ ⟨⟨by positivity, by linarith⟩, fun b hb ↦ ?_⟩, 0,
    ⟨le_rfl, hD.le⟩, fun T ↦ ?_⟩
  · rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs, abs_of_nonneg hℓ0]
    exact min_le_right _ _
  · -- the objective `η ℓ b + β (b - D / 2)² / 2` is at least its value at `D / 2` minus
    -- `η² ℓ² / (2 β) ≤ ε`
    simp only [bregDiv, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    have key : 0 ≤ 2 * β * (η * ℓ * (b - D / 2) + β / 2 * (b - D / 2) ^ 2 + ε) := by
      nlinarith [sq_nonneg (β * (b - D / 2) + η * ℓ)]
    have := (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 2 * β)).mp key
    nlinarith
  · -- the regret against `0` is `T ℓ D / 2`
    have h_reg : regret (fun t b ↦ (ℓ • ContinuousLinearMap.id ℝ ℝ) b) (fun _ ↦ D / 2) 0 T =
        T * D * ℓ / 2 := by
      simp only [regret_def, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_zero,
        sub_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    rw [h_reg]
    have hTD : 0 ≤ (T : ℝ) * D := by positivity
    have h1 : T * D * √(β * ε) / η ≤ T * D * (√(2 * β * ε) / η) := by
      rw [← mul_div_assoc]
      gcongr
      nlinarith [mul_pos hβ hε]
    have h2 : min (T * D * √(β * ε) / η) (D * T) ≤ T * D * ℓ := by
      rw [hℓ, mul_min_of_nonneg _ _ hTD, mul_one]
      exact min_le_min h1 (le_of_eq (mul_comm _ _))
    linarith

end Schlisselberg2026Hidden
