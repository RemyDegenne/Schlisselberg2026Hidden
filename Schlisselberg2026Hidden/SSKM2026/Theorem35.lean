/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent
public import Schlisselberg2026Hidden.ForLMLExplore.Analysis.Convex.PowerBarrier
public import LMLExplore.Analysis.Convex.Simplex
public import Schlisselberg2026Hidden.SSKM2026.Lemma34

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
  classical
  obtain ⟨i₀⟩ : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  have : Nonempty α := ⟨i₀⟩
  set d : ℝ := (Fintype.card α : ℝ) with hd_def
  have hd2 : (2 : ℝ) ≤ d := by rw [hd_def]; exact_mod_cast h2
  have hd0 : 0 < d := by linarith
  set u₀ : α → ℝ := fun _ ↦ d⁻¹ with hu₀_def
  have hu₀ : u₀ ∈ simplex α := uniform_mem_simplex α
  have hu₀1 : ∑ i, u₀ i = 1 := (mem_simplex_iff.mp hu₀).2
  set ℓ₀ : α → ℝ := fun j ↦ if j = i₀ then 0 else 1 with hℓ₀_def
  have hℓ₀ : ∀ j ≠ i₀, ℓ₀ j = 1 := fun j hj ↦ by simp [hℓ₀_def, hj]
  have hℓ₀i₀ : ℓ₀ i₀ = 0 := by simp [hℓ₀_def]
  refine ⟨ℓ₀, fun i ↦ ?_, fun _ ↦ u₀, rfl, fun t ↦ ?_, Pi.single i₀ 1, single_mem_simplex i₀,
    fun v hv ↦ ?_, fun T ↦ ?_⟩
  · simp only [hℓ₀_def]
    split_ifs <;> simp
  · -- staying at the uniform point is an approximate step
    have hw : u₀ ∈ {w : α → ℝ | (∀ i, 0 < w i) ∧ ∑ i, w i = 1} :=
      ⟨fun _ ↦ inv_pos.mpr hd0, hu₀1⟩
    have h1 : (d⁻¹) ^ (1 - ν) = d ^ (ν - 1) := by
      rw [inv_rpow hd0.le, ← rpow_neg hd0.le, neg_sub]
    have hc₁d : 0 < c₁ * d ^ ν := mul_pos hr.pos (rpow_pos_of_pos hd0 ν)
    refine isApproxMirrorDescentStep_self_of_isPowerBarrier h2 hr hw (i₀ := i₀) (c := 1) hℓ₀
      (by rw [hℓ₀i₀]; norm_num) hη.le (by rw [hu₀_def]; dsimp only; rw [h1]; exact hηd) ?_
    rw [hu₀_def]
    dsimp only
    rw [inv_rpow hd0.le]
    calc 2 * η ^ 2 * (d ^ ν)⁻¹ / c₁ = 2 * η ^ 2 / (c₁ * d ^ ν) := by
          field_simp
      _ ≤ 4 * η ^ 2 / (c₁ * d ^ ν) :=
          div_le_div_of_nonneg_right (by nlinarith [sq_nonneg η]) hc₁d.le
      _ ≤ ε := hε
  · -- the vertex `i₀` minimizes the loss
    have h0 : ∑ i, ℓ₀ i * (Pi.single i₀ 1 : α → ℝ) i = 0 := by
      rw [sum_mul_eq_add_mul_of_forall_ne (by simp) hℓ₀, hℓ₀i₀]
      simp
    rw [h0]
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (by simp only [hℓ₀_def]; split_ifs <;> simp)
      ((mem_simplex_iff.mp hv).1 i)
  · -- the regret
    have hu : ∑ i, ℓ₀ i * u₀ i = 1 - d⁻¹ := by
      rw [sum_mul_eq_add_mul_of_forall_ne hu₀1 hℓ₀, hℓ₀i₀]
      ring
    have hs : ∑ i, ℓ₀ i * (Pi.single i₀ 1 : α → ℝ) i = 0 := by
      rw [sum_mul_eq_add_mul_of_forall_ne (by simp) hℓ₀, hℓ₀i₀]
      simp
    rw [regret_eq_sum_sub_sum]
    simp only [hu, hs, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_zero, sub_zero]
    have hd' : d⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]
      exact div_le_div_of_nonneg_left zero_le_one (by norm_num) hd2
    have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    nlinarith

end Schlisselberg2026Hidden
