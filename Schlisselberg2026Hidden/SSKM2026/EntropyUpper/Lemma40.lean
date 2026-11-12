/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.SSKM2026.EntropyUpper.Lemma13
public import Schlisselberg2026Hidden.SSKM2026.EntropyUpper.Lemma24
public import Schlisselberg2026Hidden.SSKM2026.EntropyUpper.Lemma33

/-!
# Lemma 40 of [SSKM26]: the weight of a balanced arm stays away from zero

Let `a` be an `ε`-approximate trajectory of mirror descent on the simplex with the negative
entropy, started at the uniform point, with positive coordinates up to round `T ≥ 1`, learning
rate `0 ≤ η ≤ 1/16` and losses with coordinates in `[-1, 1]`. Let the arm `j` be `A`-balanced:
`L_{[s,t)}(j) - L_{[s,t)}(i) ≤ A` for all `s ≤ t ≤ T` and all arms `i`. With
`ξ = e^{-(η A + 1)} / d`, if `ε ≤ ξ / (32 T²)`, then the weight of `j` stays at least `ξ` up to
round `T` [SSKM26, Lemma 40]. The arm `j` need not be a best arm.

The proof is by strong induction on the round `t`. If the weight of `j` at `t` is at least its
weight at an earlier round, or if no arm has weight above `1 / d` at `t`, the bound is immediate.
Otherwise, some arm `i` has weight above `1 / d` at `t`. One step keeps half of the weight of `j`
(Lemma 25 of [SSKM26]), so the weight of `j` is at least `ξ / 2` up to `t`. The weight of `i`
stays above `ξ` up to `t`: at the last round `s` where it is at most `ξ`, the balance between `s`
and `t` (Lemma 33 of [SSKM26]) and Lemma 13 of [SSKM26] would give it a weight at most `1 / d`
at `t`. Then the balance between `0` and `t` and Lemma 13 of [SSKM26] give the weight `ξ` to
`j` at `t`.

The paper asks `ε ≤ ξ / (2 T²)` and `T ≥ 4`; with the corrected Lemmas 25 and 33 of [SSKM26] its
argument needs `ε ≤ ξ / 32` and `ε ≤ ξ / (16 T²)` (`notes/paper-errata.md`).

## Main statements

* `Schlisselberg2026Hidden.exp_neg_div_card_le_apply_of_balanced`: [SSKM26, Lemma 40],
  corrected.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α] {η ε : ℝ} {T : ℕ} {ℓ : ℕ → α → ℝ} {a : ℕ → α → ℝ}

/-- The iterates of an approximate trajectory on the simplex lie in the simplex. -/
lemma mem_simplex_of_isApproxMirrorDescentStep (ha0 : a 0 ∈ simplex α)
    (ha : ∀ t < T, IsApproxMirrorDescentStep (simplex α) negEntropy η
      (∑ i, ℓ t i • ContinuousLinearMap.proj i) (a t)
      (∑ i, log (a t i) • ContinuousLinearMap.proj i) ε (a (t + 1))) :
    ∀ t ≤ T, a t ∈ simplex α
  | 0, _ => ha0
  | t + 1, ht => (ha t ht).mem

/-- **The weight of a balanced arm stays away from zero** [SSKM26, Lemma 40], with corrected
constants. Let `a` be an `ε`-approximate trajectory of mirror descent on the simplex with the
negative entropy and learning rate `0 ≤ η ≤ 1/16`, started at the uniform point and with positive
coordinates up to round `T ≥ 1`, for losses with coordinates in `[-1, 1]`. Let the arm `j` be
`A`-balanced: `L_{[s,t)}(j) - L_{[s,t)}(i) ≤ A` for all `s ≤ t ≤ T` and all arms `i`. If
`ε ≤ ξ / (32 T²)` with `ξ = e^{-(η A + 1)} / d`, then `ξ ≤ a t j` for every `t ≤ T`. -/
lemma exp_neg_div_card_le_apply_of_balanced (ha0 : a 0 = fun _ ↦ (Fintype.card α : ℝ)⁻¹)
    (hpos : ∀ t ≤ T, ∀ k, 0 < a t k)
    (ha : ∀ t < T, IsApproxMirrorDescentStep (simplex α) negEntropy η
      (∑ i, ℓ t i • ContinuousLinearMap.proj i) (a t)
      (∑ i, log (a t i) • ContinuousLinearMap.proj i) ε (a (t + 1)))
    (hT : 1 ≤ T) (hη : 0 ≤ η) (hη' : η ≤ 1 / 16) (hℓ : ∀ t < T, ∀ k, |ℓ t k| ≤ 1) {j : α}
    {A : ℝ} (hbal : ∀ s t, s ≤ t → t ≤ T → ∀ i, ∑ r ∈ Ico s t, (ℓ r j - ℓ r i) ≤ A)
    (hε : ε ≤ exp (-(η * A + 1)) / Fintype.card α / (32 * T ^ 2)) :
    ∀ t ≤ T, exp (-(η * A + 1)) / Fintype.card α ≤ a t j := by
  classical
  have : Nonempty α := ⟨j⟩
  set d : ℝ := (Fintype.card α : ℝ) with hd_def
  have hd : 0 < d := Nat.cast_pos.2 Fintype.card_pos
  set E := exp (η * A + 1) with hE_def
  set ξ := exp (-(η * A + 1)) / d with hξ_def
  have hA : 0 ≤ A := by simpa using hbal 0 0 le_rfl (Nat.zero_le _) j
  have hE1 : 1 ≤ E := one_le_exp (by positivity)
  have hξ : ξ = d⁻¹ / E := by rw [hξ_def, hE_def, exp_neg]; field_simp
  have hξ0 : 0 < ξ := by rw [hξ]; positivity
  have hEξ : E * ξ = d⁻¹ := by rw [hξ]; field_simp
  have hξd : ξ ≤ d⁻¹ := by rw [hξ]; exact div_le_self (by positivity) hE1
  have hT0 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hmem := mem_simplex_of_isApproxMirrorDescentStep (ha0 ▸ uniform_mem_simplex α) ha
  have hε32 : ε ≤ ξ / 32 := by
    refine hε.trans (div_le_div_of_nonneg_left hξ0.le (by norm_num) ?_)
    nlinarith
  have hε16 : ε ≤ ξ / 2 / (8 * T ^ 2) := by
    refine hε.trans ?_
    have e : ξ / 2 / (8 * (T : ℝ) ^ 2) = ξ / (16 * T ^ 2) := by ring
    rw [e]
    exact div_le_div_of_nonneg_left hξ0.le (by nlinarith) (by nlinarith)
  -- the balance between two rounds, when both weights stay at least `ξ / 2`
  have h_bal (s t : ℕ) (hst : s ≤ t) (htT : t ≤ T) (i : α)
      (hψa : ∀ r, s < r → r ≤ t → ξ / 2 ≤ a r i ∧ ξ / 2 ≤ a r j) :
      log (a s j) - log (a t j) + (log (a t i) - log (a s i)) ≤ η * A + 1 := by
    have h1 := log_sub_log_add_le_sum_add_one hpos ha hT (by positivity) hε16 hst htT hψa
    have h2 := mul_le_mul_of_nonneg_left (hbal s t hst htT i) hη
    linarith
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro htT
  rcases t with _ | t
  · rw [ha0]
    exact hξd
  -- Case 1: the weight of `j` did not decrease since an earlier round
  by_cases h1 : ∃ s < t + 1, a s j ≤ a (t + 1) j
  · obtain ⟨s, hs, hsj⟩ := h1
    exact (ih s hs (hs.le.trans htT)).trans hsj
  push Not at h1
  -- Case 2: no arm has weight above `1 / d`
  by_cases h2 : ∀ i, a (t + 1) i ≤ d⁻¹
  · have h_sum : ∑ i, (d⁻¹ - a (t + 1) i) = 0 := by
      rw [sum_sub_distrib, (mem_simplex_iff.1 (hmem _ htT)).2, sum_const, card_univ,
        nsmul_eq_mul, ← hd_def, mul_inv_cancel₀ hd.ne', sub_self]
    have := (sum_eq_zero_iff_of_nonneg (fun i _ ↦ sub_nonneg.2 (h2 i))).1 h_sum j (mem_univ j)
    linarith
  -- Case 3: an arm `i` has weight above `1 / d`
  push Not at h2
  obtain ⟨i, hi⟩ := h2
  have htT' : t < T := htT
  -- (a) the weight of `j` is at least `ξ / 2` up to round `t + 1`
  have h_half : ∀ r ≤ t + 1, ξ / 2 ≤ a r j := by
    intro r hr
    rcases hr.lt_or_eq with hr | rfl
    · linarith [ih r hr (hr.le.trans htT)]
    have ht := ih t t.lt_succ_self htT'.le
    have := div_two_le_of_isApproxMirrorDescentStep_negEntropy hη hη' (hℓ t htT')
      (hmem t htT'.le) (hpos t htT'.le) (ha t htT') (i := j) (by linarith)
    linarith
  -- (b) the weight of `i` stays above `ξ` up to round `t + 1`
  have h_i : ∀ s ≤ t + 1, ξ < a s i := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s', hs', hs'i⟩ := hcon
    set s := Nat.findGreatest (fun s ↦ a s i ≤ ξ) (t + 1) with hs_def
    have hsi : a s i ≤ ξ := Nat.findGreatest_spec (P := fun s ↦ a s i ≤ ξ) hs' hs'i
    have hst : s ≤ t + 1 := Nat.findGreatest_le _
    have hst' : s < t + 1 := by
      refine hst.lt_of_ne fun h ↦ ?_
      rw [h] at hsi
      linarith
    have h_after (r : ℕ) (hr : s < r) (hrt : r ≤ t + 1) : ξ < a r i :=
      lt_of_not_ge (Nat.findGreatest_is_greatest (P := fun s ↦ a s i ≤ ξ) hr hrt)
    have hB := h_bal s (t + 1) hst htT i fun r hr hrt ↦
      ⟨by linarith [h_after r hr hrt], h_half r hrt⟩
    have := le_exp_mul_of_log_sub_log_add_le' (hpos _ htT j) (hpos s (hst.trans htT) i)
      (hpos _ htT i) (h1 s hst').le hB
    have h3 : E * a s i ≤ E * ξ := mul_le_mul_of_nonneg_left hsi (by positivity)
    linarith
  -- (c) the balance between `0` and `t + 1`
  have hB := h_bal 0 (t + 1) (Nat.zero_le _) htT i fun r _ hrt ↦
    ⟨by linarith [h_i r hrt], h_half r hrt⟩
  have h0i : a 0 i ≤ a (t + 1) i := by
    rw [ha0]
    exact hi.le
  have := le_exp_mul_of_log_sub_log_add_le (hpos 0 (Nat.zero_le _) j) (hpos _ htT j)
    (hpos 0 (Nat.zero_le _) i) h0i hB
  rw [ha0] at this
  rw [hξ, div_le_iff₀ (by positivity)]
  linarith

end Schlisselberg2026Hidden
