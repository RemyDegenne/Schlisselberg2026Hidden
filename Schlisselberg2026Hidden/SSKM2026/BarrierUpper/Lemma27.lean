/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.SSKM2026.BarrierUpper.Lemma11

/-!
# Lemma 27 of [SSKM26], corrected: the stability bound for power barriers

For a power barrier `r` with lower constant `c₁`, points `x, y` of the simplex with coordinates in
`(0, 1)`, a loss `ℓ` with coordinates in `[-1, 1]` and `η > 0`,
`⟨ℓ, x - y⟩ - D_R(y, x) / η ≤ η / c₁`, where `R w = ∑ i, r (w i)`. The regularizer is
`c₁ / 2`-strongly convex for the `ℓ¹` norm there
(`LMLExplore.IsPowerBarrier.mul_sq_sum_abs_sub_le_bregDiv`), so `D_R(y, x) ≥ c₁ L² / 4` with
`L = ‖x - y‖₁ ≥ ⟨ℓ, x - y⟩`, and `L - c₁ L² / (4 η) ≤ η / c₁`.

[SSKM26, Lemma 27] is the bound `η / 2` for a `1`-strongly convex regularizer, and the proof of
Theorem 6 of [SSKM26] applies it to power barriers, which are only `c₁ / 2`-strongly convex
(`notes/paper-errata.md`).

## Main statements

* `Schlisselberg2026Hidden.sum_mul_sub_sub_bregDiv_div_le`: [SSKM26, Lemma 27] for power
  barriers, corrected.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α] {ν c₁ c₂ : ℝ} {r : ℝ → ℝ} {η : ℝ}

/-- **The stability bound for power barriers** [SSKM26, Lemma 27], corrected. For a power barrier
`r` with lower constant `c₁`, points `x, y` of the simplex with coordinates in `(0, 1)`, a loss
with coordinates in `[-1, 1]` and `η > 0`, `⟨ℓ, x - y⟩ - D_R(y, x) / η ≤ η / c₁`, where
`R w = ∑ i, r (w i)`. -/
lemma sum_mul_sub_sub_bregDiv_div_le (hr : IsPowerBarrier ν c₁ c₂ r) {ℓ x y : α → ℝ}
    (hx : ∀ i, x i ∈ Set.Ioo 0 1) (hy : ∀ i, y i ∈ Set.Ioo 0 1) (hx1 : ∑ i, x i = 1)
    (hy1 : ∑ i, y i = 1) (hℓ : ∀ i, |ℓ i| ≤ 1) (hη : 0 < η) :
    ∑ i, ℓ i * (x i - y i) - bregDiv (fun w : α → ℝ ↦ ∑ i, r (w i)) y x
      (∑ i, deriv r (x i) • ContinuousLinearMap.proj i : (α → ℝ) →L[ℝ] ℝ) / η ≤ η / c₁ := by
  set L := ∑ i, |y i - x i| with hL
  have hD := hr.mul_sq_sum_abs_sub_le_bregDiv hx hy hx1 hy1
  have hℓL : ∑ i, ℓ i * (x i - y i) ≤ L :=
    (sum_mul_le_sum_abs hℓ _).trans_eq (sum_congr rfl fun i _ ↦ abs_sub_comm _ _)
  have h1 : c₁ / 4 * L ^ 2 / η ≤ bregDiv (fun w : α → ℝ ↦ ∑ i, r (w i)) y x
      (∑ i, deriv r (x i) • ContinuousLinearMap.proj i : (α → ℝ) →L[ℝ] ℝ) / η :=
    div_le_div_of_nonneg_right hD hη.le
  have hc₁ := hr.pos
  have h2 : L - c₁ / 4 * L ^ 2 / η ≤ η / c₁ := by
    have e : η / c₁ - (L - c₁ / 4 * L ^ 2 / η) = η / c₁ * (1 - c₁ * L / (2 * η)) ^ 2 := by
      field_simp
      ring
    have : 0 ≤ η / c₁ * (1 - c₁ * L / (2 * η)) ^ 2 := by positivity
    linarith
  linarith

end Schlisselberg2026Hidden
