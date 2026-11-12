/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent
public import LMLExplore.Analysis.Convex.NegEntropy
public import Schlisselberg2026Hidden.SSKM2026.Lemma14

/-!
# Theorem 36 of [SSKM26]: linear regret although the exact trajectory stays away from zero

On the simplex with two arms `i₁, i₂` and the negative entropy, let `0 < η ≤ 1` and
`40 τ ≤ T`. The losses put loss `1` on `i₂` for `3 τ` rounds, on `i₁` for `2 τ` rounds, then on
`i₂` again; `i₁` is the best arm and the losses are `2 τ`-balanced. The exact trajectory keeps
weight at least `1/2` on `i₁`, but for every `ε ≥ 4 η e^{-η τ}` an `ε`-approximate trajectory
gets stuck twice, first while `i₂` is good and then, after `i₁` has been pushed down by the second
phase, while `i₁` is good, and has regret at least `T / 3`.

The paper states the theorem with `k ≤ T η / 20` and `ε = 4 η e^{-k/2}` (so `τ = k / (2 η)`, which
it does not require to be an integer), `Ω(T)`, and no condition on `η`; the construction needs
`η ≤ 1` (`notes/paper-errata.md`).

## Main statements

* `Schlisselberg2026Hidden.exists_approxMirrorDescent_le_regret_negEntropy_threePhase`:
  [SSKM26, Theorem 36], corrected.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Linear regret although the exact trajectory stays away from zero** [SSKM26, Theorem 36],
corrected. Let the simplex have two arms `i₁ ≠ i₂`, let `0 < η ≤ 1` and `40 τ ≤ T`. There are
losses in `[0, 1]²` for which `i₁` is a best arm over `T` rounds and which are `2 τ`-balanced with
respect to `i₁`, such that every exact trajectory of mirror descent on the simplex with the
negative entropy and learning rate `η`, started at the uniform point, keeps weight at least `1/2`
on `i₁`, and a trajectory `a` started at the uniform point with positive coordinates which is an
`ε`-approximate trajectory for every `ε ≥ 4 η e^{-η τ}` and has regret at least `T / 3` against
the vertex `i₁`. -/
theorem exists_approxMirrorDescent_le_regret_negEntropy_threePhase (h2 : Fintype.card α = 2)
    {i₁ i₂ : α} (h12 : i₁ ≠ i₂) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {τ T : ℕ}
    (hτT : 40 * τ ≤ T) :
    ∃ ℓ : ℕ → α → ℝ, (∀ t i, ℓ t i ∈ Set.Icc 0 1) ∧
      (∀ i, ∑ t ∈ range T, ℓ t i₁ ≤ ∑ t ∈ range T, ℓ t i) ∧
      (∀ s t, s ≤ t → t ≤ T → ∀ i, ∑ r ∈ Ico s t, (ℓ r i₁ - ℓ r i) ≤ 2 * τ) ∧
      (∀ b : ℕ → α → ℝ, b 0 = (fun _ ↦ (Fintype.card α : ℝ)⁻¹) → (∀ t ≤ T, ∀ i, 0 < b t i) →
        (∀ t < T, IsMirrorDescentStep (simplex α) negEntropy η
          (∑ i, ℓ t i • ContinuousLinearMap.proj i) (b t)
          (∑ i, log (b t i) • ContinuousLinearMap.proj i) (b (t + 1))) →
        ∀ t ≤ T, 1 / 2 ≤ b t i₁) ∧
    ∃ a : ℕ → α → ℝ, a 0 = (fun _ ↦ (Fintype.card α : ℝ)⁻¹) ∧ (∀ t i, 0 < a t i) ∧
      (∀ ε, 4 * η * exp (-(η * τ)) ≤ ε → ∀ t < T,
        IsApproxMirrorDescentStep (simplex α) negEntropy η
          (∑ i, ℓ t i • ContinuousLinearMap.proj i) (a t)
          (∑ i, log (a t i) • ContinuousLinearMap.proj i) ε (a (t + 1))) ∧
      (T : ℝ) / 3 ≤ regret (fun t w ↦ ∑ i, ℓ t i * w i) a (Pi.single i₁ 1) T := by
  have : Nonempty α := ⟨i₁⟩
  have h2' : 2 ≤ Fintype.card α := h2.ge
  have hτT5 : 5 * τ ≤ T := by omega
  have hτ0 : (0 : ℝ) ≤ τ := Nat.cast_nonneg τ
  -- the second phase, where the loss is on `i₁`
  set P : ℕ → Prop := fun s ↦ 3 * τ ≤ s ∧ s < 5 * τ with hP_def
  have hcardP : ∀ s t, ((Ico s t).filter P).card ≤ 2 * τ := fun s t ↦ by
    calc ((Ico s t).filter P).card ≤ (Ico (3 * τ) (5 * τ)).card :=
          card_le_card fun r hr ↦ by
            simp only [mem_filter, hP_def] at hr
            exact mem_Ico.mpr hr.2
      _ = 2 * τ := by simp only [Nat.card_Ico]; omega
  have hcardP' : ∀ t, 2 * ((range t).filter P).card ≤ t := fun t ↦ by
    have : (range t).filter P = Ico (min t (3 * τ)) (min t (5 * τ)) := by
      ext s
      simp only [mem_filter, mem_range, mem_Ico, hP_def]
      omega
    rw [this, Nat.card_Ico]
    omega
  set ℓ : ℕ → α → ℝ := fun t j ↦
    if P t then (if j = i₁ then 1 else 0) else (if j = i₁ then 0 else 1) with hℓ_def
  -- the difference of the losses of `i₁` and of another arm
  have hℓdiff : ∀ r, ∀ i ≠ i₁, ℓ r i₁ - ℓ r i = 2 * (if P r then 1 else 0) - 1 := by
    intro r i hi
    by_cases hr : P r <;> simp [hℓ_def, hr, hi]
    norm_num
  -- the cumulative loss of `i₁` is at most that of another arm
  have hcum : ∀ t, ∀ i ≠ i₁, ∑ s ∈ range t, ℓ s i₁ ≤ ∑ s ∈ range t, ℓ s i := by
    intro t i hi
    have h := sum_congr rfl fun s (_ : s ∈ range t) ↦ hℓdiff s i hi
    rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, sum_boole, sum_const, card_range,
      nsmul_eq_mul, mul_one] at h
    have : (2 * ((range t).filter P).card : ℝ) ≤ t := by exact_mod_cast hcardP' t
    linarith
  -- the two arms are all the arms
  have huniv : (univ : Finset α) = {i₁, i₂} :=
    (eq_univ_of_card _ (by rw [card_pair h12, h2])).symm
  have hsum2 : ∀ f : α → ℝ, ∑ j, f j = f i₁ + f i₂ := fun f ↦ by rw [huniv, sum_pair h12]
  have hd1 : (Fintype.card α : ℝ) - 1 = 1 := by rw [h2]; norm_num
  -- the trajectory: `E t` is the effective cumulative difference of the losses of `i₁` and `i₂`
  set E : ℕ → ℝ := fun t ↦ ((min t (5 * τ) : ℕ) : ℝ) - (min t (3 * τ) : ℕ) - (min t τ : ℕ)
    with hE_def
  set v : ℕ → α → ℝ := fun t j ↦ if j = i₁ then -(η * E t) else 0 with hv_def
  set a : ℕ → α → ℝ := fun t ↦ softmax (v t) with ha_def
  have hasum : ∀ t, ∑ i, a t i = 1 := fun t ↦ sum_softmax _
  have hai₁ : ∀ t, a t i₁ = exp (-(η * E t)) / (exp (-(η * E t)) + 1) := fun t ↦ by
    rw [← hd1]
    exact softmax_ite_apply_self i₁ _
  have hai₁_le : ∀ t, a t i₁ ≤ 1 := fun t ↦ by
    rw [hai₁]
    exact (div_le_one (by positivity)).mpr (by linarith)
  have hstay : ∀ t, E (t + 1) = E t → a (t + 1) = a t := fun t h ↦ by
    simp only [ha_def, hv_def, h]
  have hexpτ : exp (-(η * τ)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  have hthr : ∀ ε, 4 * η * exp (-(η * τ)) ≤ ε → η ^ 2 * exp (-(η * τ)) ≤ ε := fun ε hε ↦ by
    have h3 : η ^ 2 ≤ η := by nlinarith
    nlinarith [exp_pos (-(η * τ))]
  refine ⟨ℓ, fun t i ↦ ?_, fun i ↦ ?_, fun s t _ _ i ↦ ?_, fun b hb0 _ hb t ht ↦ ?_, a, ?_,
    fun t i ↦ softmax_pos _ _, fun ε hε t _ ↦ ?_, ?_⟩
  · -- the losses lie in `[0, 1]`
    simp only [hℓ_def]
    split_ifs <;> simp
  · -- `i₁` is a best arm
    by_cases hi : i = i₁
    · rw [hi]
    exact hcum T i hi
  · -- the losses are `2 τ`-balanced
    by_cases hi : i = i₁
    · simp [hi]
    rw [sum_congr rfl fun r _ ↦ hℓdiff r i hi]
    calc ∑ r ∈ Ico s t, (2 * (if P r then (1 : ℝ) else 0) - 1)
        ≤ ∑ r ∈ Ico s t, (if P r then (1 : ℝ) else 0) :=
          sum_le_sum fun r _ ↦ by split_ifs <;> norm_num
      _ = (((Ico s t).filter P).card : ℝ) := by rw [sum_boole]
      _ ≤ 2 * τ := by exact_mod_cast hcardP s t
  · -- every exact trajectory keeps weight at least `1 / 2` on `i₁`
    rw [eq_softmax_of_isMirrorDescentStep_negEntropy hb0 hb t ht, softmax_apply, hsum2]
    have h := hcum t i₂ h12.symm
    have hexp : exp (-(η * ∑ s ∈ range t, ℓ s i₂)) ≤ exp (-(η * ∑ s ∈ range t, ℓ s i₁)) :=
      exp_le_exp.mpr (by nlinarith)
    rw [le_div_iff₀ (by positivity)]
    linarith
  · -- the trajectory starts at the uniform point
    rw [← softmax_zero]
    simp only [ha_def, hv_def, hE_def]
    congr 1
    funext j
    simp
  · -- the steps are approximate
    have hε0 : 0 ≤ ε := le_trans (by positivity) hε
    -- an exact step, when `E` moves by `±1` in the direction of the loss
    have hexact : ∀ c : ℝ, (∀ j, ℓ t j = (if j = i₁ then (1 + c) / 2 else (1 - c) / 2)) →
        E (t + 1) = E t + c →
        IsApproxMirrorDescentStep (simplex α) negEntropy η
          (∑ i, ℓ t i • ContinuousLinearMap.proj i) (a t)
          (∑ i, log (a t i) • ContinuousLinearMap.proj i) ε (a (t + 1)) := by
      intro c hℓt hE
      refine IsMirrorDescentStep.isApproxMirrorDescentStep ?_ |>.mono hε0
      rw [isMirrorDescentStep_negEntropy_iff (softmax_mem_simplex _) (softmax_pos _)]
      simp only [ha_def]
      simp_rw [sub_eq_add_neg, softmax_log_softmax_add]
      rw [← softmax_add_const _ (-(η * ((1 - c) / 2)))]
      congr 1
      funext j
      simp only [hv_def, hℓt, hE]
      split_ifs <;> ring
    by_cases h1 : t < τ
    · refine hexact (-1) (fun j ↦ ?_) ?_
      · have : ¬P t := fun h ↦ by omega
        by_cases hj : j = i₁ <;> simp [hℓ_def, this, hj]
      · simp only [hE_def]
        rw [min_eq_left (by omega : t ≤ 5 * τ), min_eq_left (by omega : t ≤ 3 * τ),
          min_eq_left h1.le, min_eq_left (by omega : t + 1 ≤ 5 * τ),
          min_eq_left (by omega : t + 1 ≤ 3 * τ), min_eq_left (by omega : t + 1 ≤ τ)]
        push_cast
        ring
    by_cases h3 : t < 3 * τ
    · -- staying put while the loss is on `i₂` and `i₁` has a large weight
      have hE : E (t + 1) = E t := by
        simp only [hE_def]
        rw [min_eq_left (by omega : t ≤ 5 * τ), min_eq_left (by omega : t ≤ 3 * τ),
          min_eq_right (by omega : τ ≤ t), min_eq_left (by omega : t + 1 ≤ 5 * τ),
          min_eq_left (by omega : t + 1 ≤ 3 * τ), min_eq_right (by omega : τ ≤ t + 1)]
        push_cast
        ring
      have hEt : E t = -τ := by
        simp only [hE_def]
        rw [min_eq_left (by omega : t ≤ 5 * τ), min_eq_left (by omega : t ≤ 3 * τ),
          min_eq_right (by omega : τ ≤ t)]
        ring
      have hnP : ¬P t := fun h ↦ by omega
      rw [hstay t hE]
      refine isApproxMirrorDescentStep_negEntropy_self (softmax_mem_simplex _) (softmax_pos _)
        (i₀ := i₁) (by simp [hℓ_def, hnP]) (fun j hj ↦ by simp [hℓ_def, hnP, hj]) hη.le hη1 ?_
      refine le_trans ?_ (hthr ε hε)
      refine mul_le_mul_of_nonneg_left ((min_le_right _ _).trans ?_) (sq_nonneg _)
      have h := hai₁ t
      simp only [ha_def] at h
      have hX : exp (-(η * -(τ : ℝ))) = exp (η * τ) := by ring_nf
      rw [h, hEt, hX, exp_neg, one_sub_div (by positivity), add_sub_cancel_left, inv_eq_one_div]
      exact one_div_le_one_div_of_le (exp_pos _) (by linarith)
    by_cases h5 : t < 5 * τ
    · refine hexact 1 (fun j ↦ ?_) ?_
      · have : P t := ⟨by omega, h5⟩
        by_cases hj : j = i₁ <;> simp [hℓ_def, this, hj]
      · simp only [hE_def]
        rw [min_eq_left h5.le, min_eq_right (by omega : 3 * τ ≤ t),
          min_eq_right (by omega : τ ≤ t), min_eq_left (by omega : t + 1 ≤ 5 * τ),
          min_eq_right (by omega : 3 * τ ≤ t + 1), min_eq_right (by omega : τ ≤ t + 1)]
        push_cast
        ring
    · -- staying put while the loss is on `i₂` and `i₁` has a small weight
      have hE5 : ∀ s, 5 * τ ≤ s → E s = τ := fun s hs ↦ by
        simp only [hE_def]
        rw [min_eq_right hs, min_eq_right (by omega : 3 * τ ≤ s), min_eq_right (by omega : τ ≤ s)]
        push_cast
        ring
      have hnP : ¬P t := fun h ↦ by omega
      rw [hstay t (by rw [hE5 t (by omega), hE5 (t + 1) (by omega)])]
      refine isApproxMirrorDescentStep_negEntropy_self (softmax_mem_simplex _) (softmax_pos _)
        (i₀ := i₁) (by simp [hℓ_def, hnP]) (fun j hj ↦ by simp [hℓ_def, hnP, hj]) hη.le hη1 ?_
      refine le_trans ?_ (hthr ε hε)
      refine mul_le_mul_of_nonneg_left ((min_le_left _ _).trans ?_) (sq_nonneg _)
      have h := hai₁ t
      simp only [ha_def] at h
      rw [h, hE5 t (by omega)]
      exact div_le_self (exp_pos _).le (by linarith [exp_pos (-(η * τ))])
  · -- the regret
    rw [regret_eq_sum_sub_sum, ← sum_sub_distrib, ← sum_range_add_sum_Ico _ hτT5,
      ← sum_range_add_sum_Ico _ (by omega : 3 * τ ≤ 5 * τ)]
    have hsingle : ∑ i, (Pi.single i₁ 1 : α → ℝ) i = 1 := by simp
    have hround2 : ∀ t, ¬P t → ∑ i, ℓ t i * a t i - ∑ i, ℓ t i * (Pi.single i₁ 1 : α → ℝ) i =
        1 - a t i₁ := fun t ht ↦ by
      have hℓt : ∀ j ≠ i₁, ℓ t j = 1 := fun j hj ↦ by simp [hℓ_def, ht, hj]
      have hℓti : ℓ t i₁ = 0 := by simp [hℓ_def, ht]
      rw [sum_mul_eq_add_mul_of_forall_ne (hasum t) hℓt,
        sum_mul_eq_add_mul_of_forall_ne hsingle hℓt, hℓti]
      simp only [Pi.single_eq_same]
      ring
    have hA : ∀ t ∈ range (3 * τ),
        0 ≤ ∑ i, ℓ t i * a t i - ∑ i, ℓ t i * (Pi.single i₁ 1 : α → ℝ) i := fun t ht ↦ by
      rw [hround2 t fun h ↦ by have := mem_range.mp ht; omega]
      linarith [hai₁_le t]
    have hB : ∀ t ∈ Ico (3 * τ) (5 * τ),
        -1 ≤ ∑ i, ℓ t i * a t i - ∑ i, ℓ t i * (Pi.single i₁ 1 : α → ℝ) i := fun t ht ↦ by
      have hPt : P t := mem_Ico.mp ht
      have hℓt : ∀ j ≠ i₁, ℓ t j = 0 := fun j hj ↦ by simp [hℓ_def, hPt, hj]
      have hℓti : ℓ t i₁ = 1 := by simp [hℓ_def, hPt]
      rw [sum_mul_eq_add_mul_of_forall_ne (hasum t) hℓt,
        sum_mul_eq_add_mul_of_forall_ne hsingle hℓt, hℓti]
      simp only [Pi.single_eq_same]
      linarith [(softmax_pos (v t) i₁).le]
    have hC : ∀ t ∈ Ico (5 * τ) T,
        1 / 2 ≤ ∑ i, ℓ t i * a t i - ∑ i, ℓ t i * (Pi.single i₁ 1 : α → ℝ) i := fun t ht ↦ by
      have ht5 := (mem_Ico.mp ht).1
      have hEt : E t = τ := by
        simp only [hE_def]
        rw [min_eq_right ht5, min_eq_right (by omega : 3 * τ ≤ t),
          min_eq_right (by omega : τ ≤ t)]
        push_cast
        ring
      rw [hround2 t fun h ↦ by have := h.2; omega, hai₁, hEt]
      have hX : exp (-(η * τ)) / (exp (-(η * τ)) + 1) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      linarith
    have sA := sum_le_sum hA
    have sB := sum_le_sum hB
    have sC := sum_le_sum hC
    simp only [sum_const, card_range, Nat.card_Ico, nsmul_eq_mul] at sA sB sC
    rw [Nat.cast_sub (by omega : 3 * τ ≤ 5 * τ)] at sB
    rw [Nat.cast_sub hτT5] at sC
    have hT : (40 * τ : ℝ) ≤ T := by exact_mod_cast hτT
    push_cast at sB sC
    linarith

end Schlisselberg2026Hidden
