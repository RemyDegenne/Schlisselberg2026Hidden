/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.SSKM2026.EntropyUpper.Lemma22
public import LMLExplore.OnlineLearning.Regret

/-!
# Lemma 39 of [SSKM26]: regret when the best arm keeps its weight

Let `a` be an `ε`-approximate trajectory of mirror descent on the simplex with the negative
entropy, with positive coordinates up to round `T`, learning rate `0 < η ≤ 1` and losses with
coordinates in `[-1, 1]`. If the weight of an arm `j` stays at least `ξ > 0` at the rounds
`1 ≤ t ≤ T` and `ε ≤ η⁴ ξ / 16`, then
`∑ t < T, (⟨ℓ t, a t⟩ - ℓ t j) ≤ -log (a 0 j) / η + η T`; when `j` is a best arm, this bounds the
regret against every point of the simplex [SSKM26, Lemma 39].

Each round costs `η²`. The approximate first-order condition (Lemma 22 of [SSKM26]) in the
direction of the vertex `e_j`, with `u = η² ξ / 4`, costs `η² / 2`, since
`∑ k, (e_j - w') k ^ 2 / w' k = 1 / w' j - 1 ≤ 1 / ξ`; it bounds `η ⟨ℓ, w' - e_j⟩` by
`log (w' j) - log (w j) - KL(w', w) + η² / 2`. Pinsker's inequality bounds `η ⟨ℓ, w - w'⟩` by
`KL(w', w) + η² / 2` (the paper's Lemma 27, with the `1`-strong convexity of the negative entropy
for the `ℓ¹` norm). The terms `log (a t j)` telescope.

This replaces the paper's proof of Lemma 39, through the sets `S_t` of its Lemmas 37 and 38,
which has several gaps (`notes/paper-errata.md`). The paper's statement also has the comparator
term `D_R(w, w₁) / η` for every `w`, which its proof does not give, and the hypothesis
`ε ≤ η⁴ ξ' / (2 r''(ξ'))` with `ξ' = min (η / d, ξ)`.

## Main statements

* `Schlisselberg2026Hidden.mul_sum_mul_sub_le_of_isApproxMirrorDescentStep_negEntropy`: the cost
  of one round.
* `Schlisselberg2026Hidden.sum_sum_mul_sub_le_of_le_apply`,
  `Schlisselberg2026Hidden.regret_le_of_le_apply`: [SSKM26, Lemma 39], corrected.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α] {η ε ξ : ℝ}

/-- **The cost of one round against a vertex.** Let `w` be a point of the simplex with positive
coordinates, `w'` an `ε`-approximate step of mirror descent with the negative entropy from `w`,
with positive coordinates, for a loss `ℓ` with coordinates in `[-1, 1]` and learning rate
`0 < η ≤ 1`. If `ξ ≤ w' j` with `ξ > 0` and `ε ≤ η⁴ ξ / 16`, then
`η (⟨ℓ, w⟩ - ℓ j) ≤ log (w' j) - log (w j) + η²`. -/
lemma mul_sum_mul_sub_le_of_isApproxMirrorDescentStep_negEntropy {ℓ w w' : α → ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hℓ : ∀ k, |ℓ k| ≤ 1) (hw : w ∈ simplex α) (hwpos : ∀ k, 0 < w k)
    (hw'pos : ∀ k, 0 < w' k)
    (h : IsApproxMirrorDescentStep (simplex α) negEntropy η
      (∑ i, ℓ i • ContinuousLinearMap.proj i) w (∑ i, log (w i) • ContinuousLinearMap.proj i) ε w')
    {j : α} (hξ : 0 < ξ) (hξj : ξ ≤ w' j) (hε : ε ≤ η ^ 4 * ξ / 16) :
    η * (∑ k, ℓ k * w k - ℓ j) ≤ log (w' j) - log (w j) + η ^ 2 := by
  classical
  have hw' := h.mem
  have hwj := hw'pos j
  have hwj1 : w' j ≤ 1 := (simplex_subset_Icc hw').2 j
  -- the direction of the vertex `e_j`
  set v : α → ℝ := Pi.single j 1 - w' with hv
  have hv_mem : w' + v ∈ simplex α := by
    rw [hv, add_sub_cancel]
    exact single_mem_simplex j
  set u := η ^ 2 * ξ / 4 with hu_def
  have hu : 0 < u := by positivity
  have hu1 : u ≤ 1 := by
    rw [hu_def, div_le_one (by norm_num)]
    nlinarith [pow_le_one₀ hη.le hη1 (n := 2)]
  have h_fo := neg_div_sub_le_of_isApproxMirrorDescentStep_negEntropy hwpos hw'pos h hv_mem hu hu1
  -- the `χ²` term of the vertex direction is `1 / w' j - 1 ≤ 1 / ξ`
  have hQ : ∑ k, v k ^ 2 / w' k ≤ 1 / ξ := by
    have e (k : α) : v k ^ 2 / w' k = (Pi.single j (1 / w' j) : α → ℝ) k -
        2 * (Pi.single j 1 : α → ℝ) k + w' k := by
      simp only [hv, Pi.sub_apply]
      by_cases hk : k = j
      · subst hk
        simp only [Pi.single_eq_same]
        field_simp
        ring
      · simp only [Pi.single_eq_of_ne hk, zero_sub, neg_sq, mul_zero, sub_zero, zero_add]
        field_simp [(hw'pos k).ne']
    simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_pi_single', mem_univ,
      ite_true, (mem_simplex_iff.1 hw').2]
    have : 1 / w' j ≤ 1 / ξ := one_div_le_one_div_of_le hξ hξj
    linarith
  have h_err : -(η ^ 2 / 2) ≤ -ε / u - u * ∑ k, v k ^ 2 / w' k := by
    have h1 : ε / u ≤ η ^ 2 / 4 := by
      rw [div_le_iff₀ hu, hu_def]
      nlinarith
    have h2 : u * ∑ k, v k ^ 2 / w' k ≤ η ^ 2 / 4 := by
      calc u * ∑ k, v k ^ 2 / w' k ≤ u * (1 / ξ) := mul_le_mul_of_nonneg_left hQ hu.le
        _ = η ^ 2 / 4 := by
          rw [hu_def]
          field_simp
    have : -ε / u = -(ε / u) := neg_div _ _
    linarith
  -- the gradient in the vertex direction
  set KL := ∑ k, w' k * (log (w' k) - log (w k)) with hKL
  have h_grad : ∑ k, (η * ℓ k + log (w' k) - log (w k)) * v k =
      η * ℓ j + log (w' j) - log (w j) - η * ∑ k, ℓ k * w' k - KL := by
    simp only [hv, Pi.sub_apply, mul_sub, sum_sub_distrib]
    rw [Finset.sum_eq_single j (fun k _ hk ↦ by simp [hk]) (by simp)]
    simp only [Pi.single_eq_same, mul_one, hKL, mul_sum]
    have : ∑ k, (η * ℓ k + log (w' k) - log (w k)) * w' k =
        ∑ k, η * (ℓ k * w' k) + ∑ k, w' k * (log (w' k) - log (w k)) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun k _ ↦ by ring
    rw [this]
    ring
  -- Pinsker's inequality for the stability term
  have h_pinsker : η * ∑ k, ℓ k * (w k - w' k) ≤ KL + η ^ 2 / 2 := by
    have hP := sq_sum_abs_sub_le_two_mul_sum_mul_log_div hw' hw fun k hk ↦
      absurd hk (hwpos k).ne'
    have hKL' : ∑ k, w' k * log (w' k / w k) = KL := by
      refine sum_congr rfl fun k _ ↦ ?_
      rw [log_div (hw'pos k).ne' (hwpos k).ne']
    rw [hKL'] at hP
    set S := ∑ k, |w' k - w k|
    have hS : ∑ k, ℓ k * (w k - w' k) ≤ S := by
      refine sum_le_sum fun k _ ↦ ?_
      rw [abs_sub_comm]
      calc ℓ k * (w k - w' k) ≤ |ℓ k * (w k - w' k)| := le_abs_self _
        _ = |ℓ k| * |w k - w' k| := abs_mul _ _
        _ ≤ 1 * |w k - w' k| := mul_le_mul_of_nonneg_right (hℓ k) (abs_nonneg _)
        _ = |w k - w' k| := one_mul _
    nlinarith [sq_nonneg (S - η), mul_le_mul_of_nonneg_left hS hη.le]
  have h_lin : ∑ k, ℓ k * w k - ℓ j = ∑ k, ℓ k * (w k - w' k) + (∑ k, ℓ k * w' k - ℓ j) := by
    simp only [mul_sub, sum_sub_distrib]
    ring
  rw [h_lin, mul_add]
  linarith

variable {T : ℕ} {ℓ : ℕ → α → ℝ} {a : ℕ → α → ℝ}

/-- **Regret against an arm that keeps its weight** [SSKM26, Lemma 39], corrected, with a new
proof. Let `a` be an `ε`-approximate trajectory of mirror descent on the simplex with the negative
entropy and learning rate `0 < η ≤ 1`, starting in the simplex and with positive coordinates up
to round `T`, for losses with coordinates in `[-1, 1]`. If `ξ ≤ a t j` for `1 ≤ t ≤ T`, with
`ξ > 0`, and `ε ≤ η⁴ ξ / 16`, then `∑ t < T, (⟨ℓ t, a t⟩ - ℓ t j) ≤ -log (a 0 j) / η + η T`. -/
lemma sum_sum_mul_sub_le_of_le_apply (ha0 : a 0 ∈ simplex α) (hpos : ∀ t ≤ T, ∀ k, 0 < a t k)
    (ha : ∀ t < T, IsApproxMirrorDescentStep (simplex α) negEntropy η
      (∑ i, ℓ t i • ContinuousLinearMap.proj i) (a t)
      (∑ i, log (a t i) • ContinuousLinearMap.proj i) ε (a (t + 1)))
    (hη : 0 < η) (hη1 : η ≤ 1) (hℓ : ∀ t < T, ∀ k, |ℓ t k| ≤ 1) {j : α} (hξ : 0 < ξ)
    (hξa : ∀ t, 1 ≤ t → t ≤ T → ξ ≤ a t j) (hε : ε ≤ η ^ 4 * ξ / 16) :
    ∑ t ∈ range T, (∑ i, ℓ t i * a t i - ℓ t j) ≤ -log (a 0 j) / η + η * T := by
  have hmem : ∀ t ≤ T, a t ∈ simplex α := fun t ht ↦ by
    rcases t with _ | t
    · exact ha0
    · exact (ha t ht).mem
  have h_round (t : ℕ) (ht : t ∈ range T) :
      η * (∑ i, ℓ t i * a t i - ℓ t j) ≤ log (a (t + 1) j) - log (a t j) + η ^ 2 := by
    have ht' : t < T := mem_range.1 ht
    exact mul_sum_mul_sub_le_of_isApproxMirrorDescentStep_negEntropy hη hη1 (hℓ t ht')
      (hmem t ht'.le) (hpos t ht'.le) (hpos (t + 1) ht') (ha t ht') hξ
      (hξa (t + 1) (Nat.succ_pos t) ht') hε
  have h_sum := sum_le_sum h_round
  rw [← mul_sum, sum_add_distrib, sum_range_sub (fun t ↦ log (a t j)), sum_const, card_range,
    nsmul_eq_mul] at h_sum
  have h_last : log (a T j) ≤ 0 :=
    log_nonpos (hpos T le_rfl j).le ((simplex_subset_Icc (hmem T le_rfl)).2 j)
  rw [neg_div, ← sub_eq_neg_add, le_sub_iff_add_le, ← le_sub_iff_add_le',
    ← mul_le_mul_iff_right₀ hη, mul_sub, mul_div_cancel₀ _ hη.ne']
  nlinarith

/-- **Regret when a best arm keeps its weight** [SSKM26, Lemma 39], corrected. Under the
hypotheses of `sum_sum_mul_sub_le_of_le_apply`, if moreover `j` is a best arm over the `T` rounds,
then the regret against every point of the simplex is at most `-log (a 0 j) / η + η T`. -/
lemma regret_le_of_le_apply (ha0 : a 0 ∈ simplex α) (hpos : ∀ t ≤ T, ∀ k, 0 < a t k)
    (ha : ∀ t < T, IsApproxMirrorDescentStep (simplex α) negEntropy η
      (∑ i, ℓ t i • ContinuousLinearMap.proj i) (a t)
      (∑ i, log (a t i) • ContinuousLinearMap.proj i) ε (a (t + 1)))
    (hη : 0 < η) (hη1 : η ≤ 1) (hℓ : ∀ t < T, ∀ k, |ℓ t k| ≤ 1) {j : α}
    (hbest : ∀ i, ∑ t ∈ range T, ℓ t j ≤ ∑ t ∈ range T, ℓ t i) (hξ : 0 < ξ)
    (hξa : ∀ t, 1 ≤ t → t ≤ T → ξ ≤ a t j) (hε : ε ≤ η ^ 4 * ξ / 16) {u : α → ℝ}
    (hu : u ∈ simplex α) :
    regret (fun t w ↦ ∑ i, ℓ t i * w i) a u T ≤ -log (a 0 j) / η + η * T := by
  refine le_trans ?_ (sum_sum_mul_sub_le_of_le_apply ha0 hpos ha hη hη1 hℓ hξ hξa hε)
  rw [regret_def]
  simp only [sum_sub_distrib]
  -- the loss of `u` is a mixture of the losses of the arms
  have h_mix : ∑ t ∈ range T, ℓ t j ≤ ∑ t ∈ range T, ∑ i, ℓ t i * u i := by
    rw [sum_comm]
    calc ∑ t ∈ range T, ℓ t j = ∑ i, u i * ∑ t ∈ range T, ℓ t j := by
          rw [← sum_mul, (mem_simplex_iff.1 hu).2, one_mul]
      _ ≤ ∑ i, u i * ∑ t ∈ range T, ℓ t i :=
          sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hbest i) ((mem_simplex_iff.1 hu).1 i)
      _ = ∑ i, ∑ t ∈ range T, ℓ t i * u i := by
          simp only [mul_sum]
          exact sum_congr rfl fun i _ ↦ sum_congr rfl fun t _ ↦ by ring
  linarith

end Schlisselberg2026Hidden
