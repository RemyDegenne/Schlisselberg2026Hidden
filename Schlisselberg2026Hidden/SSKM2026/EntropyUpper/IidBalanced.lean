/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.SubGaussian

/-!
# The balance of i.i.d. losses, from the proof of Theorem 7 of [SSKM26]

Let the losses `ℓ t : Ω → α → ℝ` be independent and identically distributed over the rounds, with
coordinates in `[-1, 1]`. With probability at least `1 - δ`, for every best arm `i*` of the `T`
rounds, the cumulative loss of `i*` on an interval of rounds exceeds that of any arm by at most
`√(2 T log (d² (T + 1)² / δ))`, with `d` the number of arms.

The proof bounds the bridges `Z = (L_{[s,t)}(i) - L_{[s,t)}(j)) - (t - s) / T (L_{[0,T)}(i) -
L_{[0,T)}(j))`: each is a sum of `T` independent bounded variables of mean `0`, sub-Gaussian with
parameter at most `T` by Hoeffding's lemma, and Hoeffding's inequality and a union bound over the
`d² (T + 1)²` tuples `(i, j, s, t)` conclude. On the event, the optimality of `i*` removes the
drift term: no mean appears in the final bound. The paper bounds the interval sums themselves, and
controls the drift with a second deviation bound, which gives a balance `2 √(8 T log (N / δ))`
(`notes/constants-entropy-upper.md`, item L7a).

## Main statements

* `Schlisselberg2026Hidden.measureReal_le_sum_Ico_sub_sub_le`: Hoeffding's inequality for one
  bridge.
* `Schlisselberg2026Hidden.exists_measurableSet_sum_Ico_sub_le_of_iid`: [SSKM26, proof of
  Theorem 7], the balance of i.i.d. losses.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open Finset Real MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Schlisselberg2026Hidden

variable {α : Type*} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Hoeffding's inequality for a bridge** [SSKM26, proof of Theorem 7]. Let the losses `ℓ t` be
independent and identically distributed over the rounds, with coordinates in `[-1, 1]`. For
`s ≤ t ≤ T` with `T ≠ 0`, two arms `i, j` and `x ≥ 0`, the bridge
`(L_{[s,t)}(i) - L_{[s,t)}(j)) - (t - s) / T (L_{[0,T)}(i) - L_{[0,T)}(j))` is at least `x` with
probability at most `exp (-x² / (2 T))`. -/
lemma measureReal_le_sum_Ico_sub_sub_le [IsProbabilityMeasure P] (ℓ : ℕ → Ω → α → ℝ)
    (hℓ_meas : ∀ t, Measurable (ℓ t)) (hℓ_indep : iIndepFun ℓ P)
    (hℓ_ident : ∀ t, IdentDistrib (ℓ t) (ℓ 0) P P) (hℓ : ∀ t ω i, ℓ t ω i ∈ Set.Icc (-1) 1)
    {T : ℕ} (hT : T ≠ 0) {s t : ℕ} (hst : s ≤ t) (htT : t ≤ T) (i j : α) {x : ℝ}
    (hx : 0 ≤ x) :
    P.real {ω | x ≤ ∑ r ∈ Ico s t, (ℓ r ω i - ℓ r ω j) -
      ((t : ℝ) - s) / T * ∑ r ∈ range T, (ℓ r ω i - ℓ r ω j)} ≤ exp (-x ^ 2 / (2 * T)) := by
  have hT0 : (0 : ℝ) < T := Nat.cast_pos.2 (Nat.pos_of_ne_zero hT)
  set p : ℝ := ((t : ℝ) - s) / T with hp_def
  have hp0 : 0 ≤ p := div_nonneg (sub_nonneg.2 (Nat.cast_le.2 hst)) hT0.le
  have hTp : (T : ℝ) * p = t - s := by rw [hp_def]; field_simp
  -- the coefficients `c r = 𝟙[s ≤ r < t] - p` of the bridge
  set c : ℕ → ℝ := fun r ↦ (if r ∈ Ico s t then 1 else 0) - p with hc_def
  have hsub : range T ∩ Ico s t = Ico s t :=
    inter_eq_right.2 fun r hr ↦ mem_range.2 ((mem_Ico.1 hr).2.trans_le htT)
  have h_ind : ∑ r ∈ range T, (if r ∈ Ico s t then (1 : ℝ) else 0) = T * p := by
    rw [sum_ite_mem, hsub, sum_const, Nat.card_Ico, nsmul_one, Nat.cast_sub hst, hTp]
  have hc_sum : ∑ r ∈ range T, c r = 0 := by
    simp only [hc_def, sum_sub_distrib, h_ind, sum_const, card_range, nsmul_eq_mul, sub_self]
  have hc_sq : ∑ r ∈ range T, 4 * c r ^ 2 ≤ (T : ℝ) := by
    have h (r : ℕ) : c r ^ 2 = (if r ∈ Ico s t then 1 else 0) * (1 - 2 * p) + p ^ 2 := by
      simp only [hc_def]; split_ifs <;> ring
    rw [← mul_sum]
    simp only [h, sum_add_distrib, ← sum_mul, h_ind, sum_const, card_range, nsmul_eq_mul]
    nlinarith [sq_nonneg (2 * p - 1)]
  -- the summands `Y r = c r (ℓ r i - ℓ r j)` and their means
  set Y : ℕ → Ω → ℝ := fun r ω ↦ c r * (ℓ r ω i - ℓ r ω j) with hY_def
  have hg : Measurable fun v : α → ℝ ↦ v i - v j := by fun_prop
  have hY_meas (r : ℕ) : Measurable (Y r) := by
    simp only [hY_def]
    exact ((hg.comp (hℓ_meas r)).const_mul _)
  set m : ℝ := ∫ ω, (ℓ 0 ω i - ℓ 0 ω j) ∂P
  have hY_int (r : ℕ) : P[Y r] = c r * m := by
    simp only [hY_def]
    rw [integral_const_mul]
    exact congrArg _ ((hℓ_ident r).comp hg).integral_eq
  have hZ (ω : Ω) : ∑ r ∈ Ico s t, (ℓ r ω i - ℓ r ω j) - p * ∑ r ∈ range T, (ℓ r ω i - ℓ r ω j) =
      ∑ r ∈ range T, (Y r ω - P[Y r]) := by
    have h1 : ∑ r ∈ range T, (Y r ω - P[Y r]) = ∑ r ∈ range T, Y r ω := by
      rw [sum_sub_distrib, sum_congr rfl fun r _ ↦ hY_int r, ← sum_mul, hc_sum, zero_mul,
        sub_zero]
    rw [h1]
    simp only [hY_def, hc_def, sub_mul, sum_sub_distrib, ite_mul, one_mul, zero_mul, sum_ite_mem,
      hsub, ← mul_sum]
  -- Hoeffding's lemma for each summand, and Hoeffding's inequality for their sum
  have h_indep : iIndepFun (fun r ω ↦ Y r ω - P[Y r]) P :=
    hℓ_indep.comp (fun r (v : α → ℝ) ↦ c r * (v i - v j) - ∫ ω, Y r ω ∂P)
      fun r ↦ (hg.const_mul _).sub_const _
  have h_subG (r : ℕ) (_ : r ∈ range T) : HasSubgaussianMGF (fun ω ↦ Y r ω - P[Y r])
      ((‖2 * |c r| - -(2 * |c r|)‖₊ / 2) ^ 2) P := by
    refine hasSubgaussianMGF_of_mem_Icc (hY_meas r).aemeasurable (ae_of_all _ fun ω ↦ ?_)
    have h1 := hℓ r ω i
    have h2 := hℓ r ω j
    have h3 : |ℓ r ω i - ℓ r ω j| ≤ 2 :=
      abs_le.2 ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
    have h4 : |Y r ω| ≤ 2 * |c r| := by
      simp only [hY_def, abs_mul]
      nlinarith [abs_nonneg (c r)]
    exact abs_le.1 h4
  have h_param (r : ℕ) : (((‖2 * |c r| - -(2 * |c r|)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = 4 * c r ^ 2 := by
    have : |2 * |c r| - -(2 * |c r|)| = 4 * |c r| := by
      rw [abs_of_nonneg (by linarith [abs_nonneg (c r)])]; ring
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat,
      this]
    rw [div_pow, mul_pow, sq_abs]
    ring
  have h_sum := HasSubgaussianMGF.sum_of_iIndepFun h_indep h_subG
  have h_T : HasSubgaussianMGF (fun ω ↦ ∑ r ∈ range T, (Y r ω - P[Y r])) (T : ℝ≥0) P := by
    refine ⟨h_sum.integrable_exp_mul, fun u ↦ (h_sum.mgf_le u).trans (exp_le_exp.2 ?_)⟩
    gcongr
    rw [← NNReal.coe_le_coe, NNReal.coe_sum, NNReal.coe_natCast]
    simpa only [h_param] using hc_sq
  calc P.real {ω | x ≤ ∑ r ∈ Ico s t, (ℓ r ω i - ℓ r ω j) - p * ∑ r ∈ range T,
        (ℓ r ω i - ℓ r ω j)}
      = P.real {ω | x ≤ ∑ r ∈ range T, (Y r ω - P[Y r])} := by simp only [hZ]
    _ ≤ exp (-x ^ 2 / (2 * ((T : ℝ≥0) : ℝ))) := h_T.measure_ge_le hx
    _ = exp (-x ^ 2 / (2 * T)) := by rw [NNReal.coe_natCast]

variable [Fintype α]

/-- **The balance of i.i.d. losses** [SSKM26, proof of Theorem 7], with corrected constants. Let
the losses `ℓ t` be independent and identically distributed over the rounds, with coordinates in
`[-1, 1]`, and let `0 < δ ≤ 1` and `T ≠ 0`. Then there is a measurable event of probability at
least `1 - δ` on which, for every best arm `i*` over the `T` rounds, every arm `i` and all
`s ≤ t ≤ T`, `L_{[s,t)}(i*) - L_{[s,t)}(i) ≤ √(2 T log (d² (T + 1)² / δ))`, with `d` the number of
arms. -/
lemma exists_measurableSet_sum_Ico_sub_le_of_iid [IsProbabilityMeasure P] (ℓ : ℕ → Ω → α → ℝ)
    (hℓ_meas : ∀ t, Measurable (ℓ t)) (hℓ_indep : iIndepFun ℓ P)
    (hℓ_ident : ∀ t, IdentDistrib (ℓ t) (ℓ 0) P P) (hℓ : ∀ t ω i, ℓ t ω i ∈ Set.Icc (-1) 1)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {T : ℕ} (hT : T ≠ 0) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - δ ≤ P.real E ∧ ∀ ω ∈ E, ∀ iStar : α,
      (∀ i, ∑ t ∈ range T, ℓ t ω iStar ≤ ∑ t ∈ range T, ℓ t ω i) →
      ∀ s t, s ≤ t → t ≤ T → ∀ i, ∑ r ∈ Ico s t, (ℓ r ω iStar - ℓ r ω i) ≤
        √(2 * T * log ((Fintype.card α : ℝ) ^ 2 * (T + 1) ^ 2 / δ)) := by
  set N : ℝ := (Fintype.card α : ℝ) ^ 2 * (T + 1) ^ 2 with hN_def
  set A : ℝ := √(2 * T * log (N / δ)) with hA_def
  -- the tuples `(i, j, s, t)` with `s ≤ t ≤ T`, and the events that their bridge is at least `A`
  set S : Finset (α × α × ℕ × ℕ) :=
    univ ×ˢ univ ×ˢ ((range (T + 1) ×ˢ range (T + 1)).filter fun q ↦ q.1 ≤ q.2) with hS_def
  set B : α × α × ℕ × ℕ → Set Ω := fun q ↦ {ω | A ≤ ∑ r ∈ Ico q.2.2.1 q.2.2.2,
    (ℓ r ω q.1 - ℓ r ω q.2.1) - ((q.2.2.2 : ℝ) - q.2.2.1) / T *
      ∑ r ∈ range T, (ℓ r ω q.1 - ℓ r ω q.2.1)} with hB_def
  have hB_meas (q : α × α × ℕ × ℕ) : MeasurableSet (B q) := by
    have (r : ℕ) (i : α) : Measurable fun ω ↦ ℓ r ω i := (measurable_pi_apply i).comp (hℓ_meas r)
    exact measurableSet_le measurable_const (by fun_prop)
  have hU : MeasurableSet (⋃ q ∈ S, B q) := Finset.measurableSet_biUnion S fun q _ ↦ hB_meas q
  refine ⟨(⋃ q ∈ S, B q)ᶜ, hU.compl, ?_, ?_⟩
  · -- the union bound
    rw [probReal_compl_eq_one_sub hU]
    suffices ∑ q ∈ S, P.real (B q) ≤ δ by linarith [measureReal_biUnion_finset_le (μ := P) S B]
    have hcard : (#S : ℝ) ≤ N := by
      have : #S ≤ Fintype.card α * Fintype.card α * ((T + 1) * (T + 1)) := by
        rw [hS_def, card_product, card_product, card_univ, ← mul_assoc]
        gcongr
        refine (card_filter_le _ _).trans ?_
        rw [card_product, card_range]
      calc (#S : ℝ) ≤ ((Fintype.card α * Fintype.card α * ((T + 1) * (T + 1)) : ℕ) : ℝ) :=
            Nat.cast_le.2 this
        _ = N := by push_cast; ring
    have hq (q : α × α × ℕ × ℕ) (hq : q ∈ S) : P.real (B q) ≤ δ / N := by
      obtain ⟨i, j, s, t⟩ := q
      simp only [hS_def, mem_product, mem_univ, mem_filter, mem_range, true_and] at hq
      have : Nonempty α := ⟨i⟩
      have hd : (1 : ℝ) ≤ Fintype.card α := Nat.one_le_cast.2 Fintype.card_pos
      have hN1 : 1 ≤ N := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd)
        (one_le_pow₀ (by linarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)]))
      have hNδ : 1 ≤ N / δ := (one_le_div hδ).2 (hδ1.trans hN1)
      have hT0 : (0 : ℝ) < T := Nat.cast_pos.2 (Nat.pos_of_ne_zero hT)
      calc P.real (B (i, j, s, t)) ≤ exp (-A ^ 2 / (2 * T)) :=
            measureReal_le_sum_Ico_sub_sub_le ℓ hℓ_meas hℓ_indep hℓ_ident hℓ hT hq.2
              (Nat.lt_succ_iff.1 hq.1.2) i j (sqrt_nonneg _)
        _ = δ / N := by
            rw [hA_def, sq_sqrt (by have := log_nonneg hNδ; positivity),
              show -(2 * T * log (N / δ)) / (2 * T) = -log (N / δ) by field_simp, exp_neg,
              exp_log (by linarith), inv_div]
    calc ∑ q ∈ S, P.real (B q) ≤ ∑ q ∈ S, δ / N := sum_le_sum hq
      _ = #S * (δ / N) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ δ := by
          rcases (Nat.cast_nonneg #S : (0 : ℝ) ≤ #S).eq_or_lt with h | h
          · rw [← h, zero_mul]; exact hδ.le
          · calc (#S : ℝ) * (δ / N) ≤ N * (δ / N) := by gcongr
              _ = δ := by field_simp [(h.trans_le hcard).ne']
  · -- on the event, the optimality of `i*` removes the drift
    intro ω hω iStar hbest s t hst htT i
    have hmem : (iStar, i, s, t) ∈ S := by
      simp only [hS_def, mem_product, mem_univ, mem_filter, mem_range, true_and]
      exact ⟨⟨Nat.lt_succ_of_le hst |>.trans_le (Nat.succ_le_succ htT), Nat.lt_succ_of_le htT⟩,
        hst⟩
    have hlt : ¬ A ≤ _ := fun h ↦ hω (Set.mem_biUnion hmem h)
    have hdrift : ∑ r ∈ range T, (ℓ r ω iStar - ℓ r ω i) ≤ 0 := by
      rw [sum_sub_distrib]; linarith [hbest i]
    have hp : 0 ≤ ((t : ℝ) - s) / T := div_nonneg (sub_nonneg.2 (Nat.cast_le.2 hst)) T.cast_nonneg
    have := mul_nonpos_of_nonneg_of_nonpos hp hdrift
    simp only at hlt
    linarith

end Schlisselberg2026Hidden
