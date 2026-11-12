/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.Analysis.Convex.PowerBarrier

/-!
# Lemma 12 of [SSKM26], corrected: from balance to a lower bound on the coordinates

Let `r` be a power barrier with exponent `ν > 1` and lower constant `c₁`, and let `q, y` have
coordinates in `(0, 1)`, those of `q` at least `m > 0`. The quantity
`S_q(y) = ⟨∇R(q) - ∇R(y), q - y⟩ = ∑ i, (r' (q i) - r' (y i)) (q i - y i)` is a sum of nonnegative
terms, since `r'` is increasing. If `S_q(y) ≤ κ`, then every coordinate of `y` is at least every
`ψ > 0` with `(2 / m)^{ν-1} + 2 (ν - 1) κ / (c₁ m) ≤ ψ^{1-ν}`: a coordinate below `ψ` makes its
term exceed `κ`, by the corrected Lemma 41
(`LMLExplore.IsPowerBarrier.mul_rpow_sub_rpow_le_deriv_sub`).

[SSKM26, Lemma 12] bounds `-r' (y i)` through a minimizing coordinate of the balance, and its
main-text form uses Lemma 41 without the factor `1 / (ν - 1)` (`notes/paper-errata.md`). The
termwise argument avoids the minimizing coordinate.

## Main statements

* `Schlisselberg2026Hidden.le_of_sum_deriv_sub_mul_sub_le`: [SSKM26, Lemma 12], corrected.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α] {ν c₁ c₂ : ℝ} {r : ℝ → ℝ}

/-- The terms of `⟨∇R(q) - ∇R(y), q - y⟩` are nonnegative for a power barrier, on `(0, 1)`. -/
lemma deriv_sub_mul_sub_nonneg (hr : IsPowerBarrier ν c₁ c₂ r) {x y : ℝ} (hx : x ∈ Set.Ioo 0 1)
    (hy : y ∈ Set.Ioo 0 1) : 0 ≤ (deriv r x - deriv r y) * (x - y) := by
  rcases le_total y x with h | h
  · exact mul_nonneg (sub_nonneg.mpr (hr.strictMonoOn_deriv.monotoneOn hy hx h))
      (sub_nonneg.mpr h)
  · exact mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr (hr.strictMonoOn_deriv.monotoneOn hx hy h)) (sub_nonpos.mpr h)

/-- If `(2 / m)^{ν-1} + 2 (ν - 1) κ / (c₁ m) ≤ ψ^{1-ν}` with `ν > 1`, `m, c₁ > 0` and `κ ≥ 0`,
then `ψ ≤ m / 2`. -/
lemma le_half_of_add_le_rpow (hc₁ : 0 < c₁) (hν : 1 < ν) {m κ ψ : ℝ} (hm : 0 < m)
    (hκ : 0 ≤ κ)
    (hψΨ : (2 / m) ^ (ν - 1) + 2 * (ν - 1) * κ / (c₁ * m) ≤ ψ ^ (1 - ν)) : ψ ≤ m / 2 := by
  have hν1 : 0 < ν - 1 := sub_pos.mpr hν
  have hm2 : (2 / m) ^ (ν - 1) = (m / 2) ^ (1 - ν) := by
    rw [show 1 - ν = -(ν - 1) by ring, rpow_neg (by positivity), ← inv_rpow (by positivity),
      inv_div]
  have hc : 0 ≤ 2 * (ν - 1) * κ / (c₁ * m) := by positivity
  by_contra! h
  have := rpow_lt_rpow_of_neg (by positivity) h (by linarith : 1 - ν < 0)
  linarith

/-- **From balance to a lower bound on the coordinates** [SSKM26, Lemma 12], corrected. Let `r`
be a power barrier with exponent `ν > 1` and lower constant `c₁`, `q, y` with coordinates in
`(0, 1)`, those of `q` at least `m > 0`, and `κ ≥ 0`. If
`∑ i, (r' (q i) - r' (y i)) (q i - y i) ≤ κ`, then every coordinate of `y` is at least every
`ψ` with `(2 / m)^{ν-1} + 2 (ν - 1) κ / (c₁ m) ≤ ψ^{1-ν}`. -/
lemma le_of_sum_deriv_sub_mul_sub_le (hr : IsPowerBarrier ν c₁ c₂ r) (hν : 1 < ν)
    {q y : α → ℝ} (hq : ∀ i, q i ∈ Set.Ioo 0 1) (hy : ∀ i, y i ∈ Set.Ioo 0 1) {m κ ψ : ℝ}
    (hm : 0 < m) (hmq : ∀ i, m ≤ q i) (hκ : 0 ≤ κ)
    (hψΨ : (2 / m) ^ (ν - 1) + 2 * (ν - 1) * κ / (c₁ * m) ≤ ψ ^ (1 - ν))
    (hS : ∑ i, (deriv r (q i) - deriv r (y i)) * (q i - y i) ≤ κ) (i : α) : ψ ≤ y i := by
  have hi : (deriv r (q i) - deriv r (y i)) * (q i - y i) ≤ κ :=
    (single_le_sum (f := fun j ↦ (deriv r (q j) - deriv r (y j)) * (q j - y j))
      (fun j _ ↦ deriv_sub_mul_sub_nonneg hr (hq j) (hy j)) (mem_univ i)).trans hS
  by_contra! hlt
  have hν1 : 0 < ν - 1 := sub_pos.mpr hν
  have hneg : 1 - ν < 0 := by linarith
  have hm2 : (2 / m) ^ (ν - 1) = (m / 2) ^ (1 - ν) := by
    rw [show 1 - ν = -(ν - 1) by ring, rpow_neg (by positivity), ← inv_rpow (by positivity),
      inv_div]
  have hψm := le_half_of_add_le_rpow hr.pos hν hm hκ hψΨ
  have hyq : y i < q i := by linarith [hmq i]
  have h3 := hr.mul_rpow_sub_rpow_le_deriv_sub hν (hy i) (hq i) hyq.le
  have h4 : ψ ^ (1 - ν) < y i ^ (1 - ν) := rpow_lt_rpow_of_neg (hy i).1 hlt hneg
  have h5 : q i ^ (1 - ν) ≤ (m / 2) ^ (1 - ν) :=
    rpow_le_rpow_of_nonpos (by positivity) (by linarith [hmq i]) hneg.le
  have h6 : 2 * κ / m < deriv r (q i) - deriv r (y i) := by
    have e : c₁ / (ν - 1) * (2 * (ν - 1) * κ / (c₁ * m)) = 2 * κ / m := by
      have := hr.pos.ne'
      have := hν1.ne'
      field_simp
    have h7 : c₁ / (ν - 1) * (2 * (ν - 1) * κ / (c₁ * m)) <
        c₁ / (ν - 1) * (y i ^ (1 - ν) - q i ^ (1 - ν)) :=
      mul_lt_mul_of_pos_left (by linarith) (div_pos hr.pos hν1)
    linarith
  have h8 : m / 2 < q i - y i := by linarith [hmq i]
  have h9 : 2 * κ / m * (m / 2) = κ := by field_simp
  have h10 : 0 ≤ 2 * κ / m := by positivity
  nlinarith [mul_pos (sub_pos.mpr h6) (half_pos hm), mul_pos (h10.trans_lt h6) (sub_pos.mpr h8)]

end Schlisselberg2026Hidden
