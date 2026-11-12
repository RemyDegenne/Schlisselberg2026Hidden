/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.SSKM2026.EntropyUpper.Lemma22
public import Schlisselberg2026Hidden.ForLMLExplore.Analysis.Real.Sqrt

/-!
# Lemmas 24 and 25 of [SSKM26] for the negative entropy: one step moves little

Let `w'` be an `ε`-approximate mirror descent step on the simplex with the negative entropy from a
point `w` of the simplex with positive coordinates, for a loss with coordinates in `[-1, 1]` and
learning rate `η ≥ 0`. If a coordinate decreases, it decreases by at most
`4 η w i + √(2 ε w i)` [SSKM26, Lemma 24]. Hence for `η ≤ 1/16` and `ε ≤ w i / 32`, the step keeps
at least half of the coordinate: `w i / 2 ≤ w' i` [SSKM26, Lemma 25].

The proof compares `w'` with the point `w̃` that restores the coordinate `i` to `w i` and moves
each increased coordinate back towards `w` by the same fraction `λ = (w i - w' i) / P`, with `P`
the total increase. Then `‖w' - w̃‖₁ = 2 (w i - w' i)`, and `D(w', w) - D(w̃, w)` is at least
`(w i - w' i) ^ 2 / (2 w i)` by Lemma 21 of [SSKM26]; the step condition at `w̃` and Lemma 23 of
[SSKM26] conclude. The paper restores the coordinate by a prefix construction instead.

The paper's Lemma 24 has `√(ε / h)` with `h = 1 / w i` in place of `√(2 ε / h)`, and is false
with that constant; its Lemma 25 asks `ε ≤ w i / 16`, which its proof does not support with the
corrected Lemma 24 (`notes/paper-errata.md`).

## Main statements

* `Schlisselberg2026Hidden.sub_le_of_isApproxMirrorDescentStep_negEntropy`: [SSKM26, Lemma 24],
  corrected, for the negative entropy.
* `Schlisselberg2026Hidden.div_two_le_of_isApproxMirrorDescentStep_negEntropy`:
  [SSKM26, Lemma 25], forward direction, for the negative entropy.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α] {η ε : ℝ} {ℓ w w' : α → ℝ}

/-- **One step decreases a coordinate by little** [SSKM26, Lemma 24], with the corrected
constant, for the negative entropy. Let `w` be a point of the simplex with positive coordinates,
`w'` an `ε`-approximate step from `w` for a loss `ℓ` with coordinates in `[-1, 1]` and learning
rate `η ≥ 0`. If `w' i ≤ w i`, then `w i - w' i ≤ 4 η w i + √(2 ε w i)`. -/
lemma sub_le_of_isApproxMirrorDescentStep_negEntropy (hη : 0 ≤ η) (hℓ : ∀ i, |ℓ i| ≤ 1)
    (hw : w ∈ simplex α) (hwpos : ∀ i, 0 < w i)
    (h : IsApproxMirrorDescentStep (simplex α) negEntropy η
      (∑ i, ℓ i • ContinuousLinearMap.proj i) w (∑ i, log (w i) • ContinuousLinearMap.proj i) ε w')
    {i : α} (hi : w' i ≤ w i) :
    w i - w' i ≤ 4 * η * w i + √(2 * ε * w i) := by
  classical
  have hε := h.nonneg
  set Δ := w i - w' i with hΔ
  rcases (sub_nonneg.2 hi).eq_or_lt with hΔ0 | hΔ0
  · have : Δ = 0 := by rw [hΔ]; linarith
    rw [this]
    have := hwpos i
    positivity
  have hw' := h.mem
  -- the increases `p k` of the coordinates and their total `P ≥ Δ`
  set p : α → ℝ := fun k ↦ max (w' k - w k) 0 with hp
  set P := ∑ k, p k with hP
  have hp0 (k : α) : 0 ≤ p k := le_max_right _ _
  have hpi : p i = 0 := max_eq_right (by linarith)
  have hPΔ : Δ ≤ P := by
    have h_mass : ∑ k, (w' k - w k) = 0 := by
      rw [sum_sub_distrib, (mem_simplex_iff.1 hw').2, (mem_simplex_iff.1 hw).2, sub_self]
    have h_split : P = ∑ k, (w' k - w k) + ∑ k, max (w k - w' k) 0 := by
      rw [hP, ← sum_add_distrib]
      refine sum_congr rfl fun k _ ↦ ?_
      simp only [hp]
      rcases le_total (w' k) (w k) with hk | hk
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
        ring
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
        ring
    rw [h_split, h_mass, zero_add]
    calc Δ = max (w i - w' i) 0 := (max_eq_left hΔ0.le).symm
      _ ≤ ∑ k, max (w k - w' k) 0 :=
        single_le_sum (f := fun k ↦ max (w k - w' k) 0) (fun k _ ↦ le_max_right _ _) (mem_univ i)
  have hP0 : 0 < P := hΔ0.trans_le hPΔ
  set c := Δ / P with hc
  have hc0 : 0 < c := div_pos hΔ0 hP0
  have hc1 : c ≤ 1 := (div_le_one hP0).2 hPΔ
  -- the comparison point `w̃`
  set wt : α → ℝ := fun k ↦ w' k + (Pi.single i Δ : α → ℝ) k - c * p k with hwt
  have hwt_i : wt i = w i := by simp [hwt, hpi, hΔ]
  have hwt_ne (k : α) (hk : k ≠ i) : wt k = w' k - c * p k := by simp [hwt, hk]
  -- for a coordinate `k ≠ i`, `w̃ k` lies between `w k` and `w' k` when `w' k > w k`, and equals
  -- `w' k` otherwise
  have hwt_cases (k : α) (hk : k ≠ i) :
      (w k < w' k ∧ w k ≤ wt k ∧ wt k ≤ w' k) ∨ (w' k ≤ w k ∧ wt k = w' k) := by
    rw [hwt_ne k hk]
    rcases lt_or_ge (w k) (w' k) with hlt | hge
    · left
      have hpk : p k = w' k - w k := max_eq_left (by linarith)
      rw [hpk]
      refine ⟨hlt, ?_, ?_⟩ <;> nlinarith
    · right
      have hpk : p k = 0 := max_eq_right (by linarith)
      exact ⟨hge, by rw [hpk, mul_zero, sub_zero]⟩
  have hwt_mem : wt ∈ simplex α := by
    refine mem_simplex_iff.2 ⟨fun k ↦ ?_, ?_⟩
    · by_cases hk : k = i
      · rw [hk, hwt_i]
        exact (hwpos i).le
      rcases hwt_cases k hk with ⟨-, h1, -⟩ | ⟨-, h2⟩
      · exact (hwpos k).le.trans h1
      · rw [h2]
        exact (mem_simplex_iff.1 hw').1 k
    · simp only [hwt, sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_pi_single',
        mem_univ, ite_true, (mem_simplex_iff.1 hw').2]
      rw [← hP, hc, div_mul_cancel₀ _ hP0.ne']
      ring
  -- the step condition at `w̃`
  have h_le := h.le_add wt hwt_mem
  rw [bregDiv_negEntropy_pi_eq fun k h ↦ absurd h (hwpos k).ne',
    bregDiv_negEntropy_pi_eq fun k h ↦ absurd h (hwpos k).ne', sum_smul_proj_apply,
    sum_smul_proj_apply] at h_le
  -- the linear part: `⟨ℓ, w' - w̃⟩ ≥ -2 Δ`
  have h_lin : -(2 * Δ) ≤ ∑ k, ℓ k * w' k - ∑ k, ℓ k * wt k := by
    have hs : ∑ k, ℓ k * (Pi.single i Δ : α → ℝ) k = ℓ i * Δ := by
      rw [Finset.sum_eq_single i (fun k _ hk ↦ by simp [hk]) (by simp)]
      simp
    have e : ∑ k, ℓ k * w' k - ∑ k, ℓ k * wt k = c * ∑ k, ℓ k * p k - Δ * ℓ i := by
      simp only [hwt, mul_sub, mul_add, sum_sub_distrib, sum_add_distrib, hs, mul_sum]
      have : ∑ k, ℓ k * (c * p k) = ∑ k, c * (ℓ k * p k) := sum_congr rfl fun k _ ↦ by ring
      rw [this]
      ring
    have h1 : -P ≤ ∑ k, ℓ k * p k := by
      rw [hP, ← sum_neg_distrib]
      refine sum_le_sum fun k _ ↦ ?_
      have := neg_le_of_abs_le (hℓ k)
      nlinarith [hp0 k]
    have h2 : ℓ i ≤ 1 := (abs_le.1 (hℓ i)).2
    have h3 : c * P = Δ := div_mul_cancel₀ _ hP0.ne'
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left h1 hc0.le]
  -- the divergence part: `D(w', w) - D(w̃, w) ≥ Δ ^ 2 / (2 w i)`
  set f : α → ℝ := fun k ↦ (w' k * log (w' k / w k) - w' k + w k) -
    (wt k * log (wt k / w k) - wt k + w k) with hf
  have hf_nonneg (k : α) : 0 ≤ f k := by
    simp only [hf, sub_nonneg]
    by_cases hk : k = i
    · rw [hk, hwt_i, div_self (hwpos i).ne', log_one, mul_zero, zero_sub, neg_add_cancel]
      exact mul_log_div_sub_add_nonneg ((mem_simplex_iff.1 hw').1 i) (hwpos i)
    rcases hwt_cases k hk with ⟨-, h1, h2⟩ | ⟨-, h2⟩
    · exact mul_log_div_sub_add_le_of_le (hwpos k) h1 h2
    · rw [h2]
  have hf_i : Δ ^ 2 / (2 * w i) ≤ f i := by
    simp only [hf, hwt_i, div_self (hwpos i).ne', log_one, mul_zero, zero_sub, neg_add_cancel,
      sub_zero]
    exact sq_div_two_mul_le_mul_log_div_sub_add ((mem_simplex_iff.1 hw').1 i) hi (hwpos i)
  have h_div : Δ ^ 2 / (2 * w i) ≤ ∑ k, (w' k * log (w' k / w k) - w' k + w k) -
      ∑ k, (wt k * log (wt k / w k) - wt k + w k) := by
    rw [← sum_sub_distrib]
    exact hf_i.trans (single_le_sum (fun k _ ↦ hf_nonneg k) (mem_univ i))
  -- Lemma 23 of [SSKM26]
  have h_quad : 1 / (2 * w i) * Δ ^ 2 ≤ 2 * η * Δ + ε := by
    have : 1 / (2 * w i) * Δ ^ 2 = Δ ^ 2 / (2 * w i) := by ring
    nlinarith [mul_le_mul_of_nonneg_left h_lin hη]
  have := Real.le_div_add_sqrt_div_of_mul_sq_le (by have := hwpos i; positivity)
    (by positivity) hε h_quad
  have e1 : 2 * η / (1 / (2 * w i)) = 4 * η * w i := by
    field_simp
    ring
  have e2 : ε / (1 / (2 * w i)) = 2 * ε * w i := by
    field_simp
  rwa [e1, e2] at this

/-- **One step keeps half of a coordinate** [SSKM26, Lemma 25], forward direction, for the
negative entropy, with the corrected hypothesis `ε ≤ w i / 32`. Let `w` be a point of the simplex
with positive coordinates, `w'` an `ε`-approximate step from `w` for a loss `ℓ` with coordinates
in `[-1, 1]` and learning rate `0 ≤ η ≤ 1/16`. Then `w i / 2 ≤ w' i`. -/
lemma div_two_le_of_isApproxMirrorDescentStep_negEntropy (hη : 0 ≤ η) (hη' : η ≤ 1 / 16)
    (hℓ : ∀ i, |ℓ i| ≤ 1) (hw : w ∈ simplex α) (hwpos : ∀ i, 0 < w i)
    (h : IsApproxMirrorDescentStep (simplex α) negEntropy η
      (∑ i, ℓ i • ContinuousLinearMap.proj i) w (∑ i, log (w i) • ContinuousLinearMap.proj i) ε w')
    {i : α} (hεi : ε ≤ w i / 32) :
    w i / 2 ≤ w' i := by
  have hwi := hwpos i
  rcases le_total (w' i) (w i) with hi | hi
  · have h1 := sub_le_of_isApproxMirrorDescentStep_negEntropy hη hℓ hw hwpos h hi
    have h2 : √(2 * ε * w i) ≤ w i / 4 := by
      rw [sqrt_le_left (by positivity)]
      nlinarith
    nlinarith
  · linarith

end Schlisselberg2026Hidden
