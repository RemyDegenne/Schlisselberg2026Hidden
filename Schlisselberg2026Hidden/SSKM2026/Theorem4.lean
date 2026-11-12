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
# Theorem 4 of [SSKM26]: the negative entropy needs exponentially small errors

On the simplex with at least two arms and the negative entropy, for every `η > 0` and every
`ε ≥ 4 η e^{-η T / 3}`, there are losses in `[0, 1]^d` and an `ε`-approximate trajectory of mirror
descent started at the uniform point whose regret against the best point in hindsight is at
least `T / 10`: errors that are not exponentially small in `η T` can cause linear regret.

For `η ≤ 1` this is Lemma 14 of [SSKM26] with `A = T / 3`, which gives `T / 6`. For `η > 1`,
exact mirror descent on alternating losses already has regret at least `T / 10`.

The paper states the regret as `Ω(T)` and proves it through Lemma 14 of [SSKM26], which is for two
arms and needs `η ≤ 1` (`notes/paper-errata.md`).

## Main statements

* `Schlisselberg2026Hidden.exists_approxMirrorDescent_le_regret_negEntropy`:
  [SSKM26, Theorem 4], with explicit constants.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α]

/-- The partial sums of the alternating sequence `1, -1, 1, …` are `0` and `1`. -/
lemma sum_range_ite_even (t : ℕ) :
    ∑ s ∈ range t, (if Even s then (1 : ℝ) else -1) = if Even t then 0 else 1 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ, ih]
    by_cases ht : Even t
    · have : ¬Even (t + 1) := Nat.not_even_iff_odd.mpr ht.add_one
      simp [ht, this]
    · have : Even (t + 1) := (Nat.not_even_iff_odd.mp ht).add_one
      simp [ht, this]

/-- **Exact mirror descent with a large learning rate has linear regret**: for `η ≥ 1`, the
exact trajectory of mirror descent with the negative entropy from the uniform point, on the losses
`1 - e_{i₂}` at even rounds and `1 - e_{i₁}` at odd rounds, has regret at least `T / 10` against
the best vertex `e_{i₂}`. This gives [SSKM26, Theorem 4] for `η > 1`, where Lemma 14 of [SSKM26]
does not apply; every `ε ≥ 0` works. -/
lemma exists_mirrorDescent_le_regret_negEntropy_of_one_le (h2 : 2 ≤ Fintype.card α) {η ε : ℝ}
    (hη : 1 ≤ η) (T : ℕ) (hε : 0 ≤ ε) :
    ∃ ℓ : ℕ → α → ℝ, (∀ t i, ℓ t i ∈ Set.Icc 0 1) ∧
    ∃ a : ℕ → α → ℝ, a 0 = (fun _ ↦ (Fintype.card α : ℝ)⁻¹) ∧ (∀ t i, 0 < a t i) ∧
      (∀ t < T, IsApproxMirrorDescentStep (simplex α) negEntropy η
        (∑ i, ℓ t i • ContinuousLinearMap.proj i) (a t)
        (∑ i, log (a t i) • ContinuousLinearMap.proj i) ε (a (t + 1))) ∧
    ∃ u ∈ simplex α, (∀ v ∈ simplex α,
        ∑ t ∈ range T, ∑ i, ℓ t i * u i ≤ ∑ t ∈ range T, ∑ i, ℓ t i * v i) ∧
      (T : ℝ) / 10 ≤ regret (fun t w ↦ ∑ i, ℓ t i * w i) a u T := by
  classical
  obtain ⟨i₁, i₂, h12⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card α)
  have : Nonempty α := ⟨i₁⟩
  set ℓ : ℕ → α → ℝ := fun t j ↦
    if Even t then (if j = i₂ then 0 else 1) else (if j = i₁ then 0 else 1) with hℓ_def
  set a : ℕ → α → ℝ := fun t ↦ softmax fun j ↦ -(η * ∑ s ∈ range t, ℓ s j) with ha_def
  have hasum : ∀ t, ∑ i, a t i = 1 := fun t ↦ sum_softmax _
  -- the difference of the cumulative losses of `i₁` and `i₂`
  have hdiff : ∀ t, ∑ s ∈ range t, ℓ s i₁ = ∑ s ∈ range t, ℓ s i₂ + if Even t then 0 else 1 := by
    intro t
    rw [← sum_range_ite_even, ← sum_add_distrib]
    refine sum_congr rfl fun s _ ↦ ?_
    by_cases hs : Even s <;> simp [hℓ_def, hs, h12, h12.symm]
  -- the weights of `i₁` and `i₂`
  have hpair : ∀ t, a t i₁ + a t i₂ ≤ 1 := fun t ↦ by
    rw [← hasum t, ← sum_pair h12]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ ↦ (softmax_pos _ i).le
  have hratio : ∀ t, a t i₁ = exp (-(η * if Even t then 0 else 1)) * a t i₂ := fun t ↦ by
    simp only [ha_def, softmax_apply, hdiff t]
    rw [← mul_div_assoc, ← exp_add]
    congr 2
    ring
  have hbest : ∀ i, ∑ t ∈ range T, ℓ t i₂ ≤ ∑ t ∈ range T, ℓ t i := by
    intro i
    by_cases hi1 : i = i₁
    · rw [hi1, hdiff T]
      split_ifs <;> norm_num
    by_cases hi2 : i = i₂
    · rw [hi2]
    refine sum_le_sum fun t _ ↦ ?_
    by_cases ht : Even t <;> simp [hℓ_def, ht, hi1, hi2]
    split_ifs <;> norm_num
  refine ⟨ℓ, fun t i ↦ ?_, a, ?_, fun t i ↦ softmax_pos _ _, fun t _ ↦ ?_, Pi.single i₂ 1,
    single_mem_simplex i₂, fun v hv ↦ sum_sum_mul_single_le hbest hv, ?_⟩
  · simp only [hℓ_def]
    split_ifs <;> simp
  · rw [← softmax_zero]
    simp only [ha_def]
    congr 1
    funext j
    simp
  · exact (isMirrorDescentStep_negEntropy_softmax ℓ η t).isApproxMirrorDescentStep.mono hε
  · -- the regret
    rw [regret_eq_sum_sub_sum, ← sum_sub_distrib]
    have hsingle : ∑ i, (Pi.single i₂ 1 : α → ℝ) i = 1 := by simp
    have hround : ∀ t ∈ range T, (if Even t then (1 / 2 : ℝ) else -(3 / 10)) ≤
        ∑ i, ℓ t i * a t i - ∑ i, ℓ t i * (Pi.single i₂ 1 : α → ℝ) i := by
      intro t _
      by_cases ht : Even t
      · have hℓt : ∀ j ≠ i₂, ℓ t j = 1 := fun j hj ↦ by simp [hℓ_def, ht, hj]
        have hℓti : ℓ t i₂ = 0 := by simp [hℓ_def, ht]
        rw [sum_mul_eq_add_mul_of_forall_ne (hasum t) hℓt,
          sum_mul_eq_add_mul_of_forall_ne hsingle hℓt, hℓti]
        simp only [ht, ite_true]
        have h := hratio t
        simp only [ht, ite_true, mul_zero, neg_zero, exp_zero, one_mul] at h
        have := hpair t
        simp only [Pi.single_eq_same]
        linarith
      · have hℓt : ∀ j ≠ i₁, ℓ t j = 1 := fun j hj ↦ by simp [hℓ_def, ht, hj]
        have hℓti : ℓ t i₁ = 0 := by simp [hℓ_def, ht]
        rw [sum_mul_eq_add_mul_of_forall_ne (hasum t) hℓt,
          sum_mul_eq_add_mul_of_forall_ne hsingle hℓt, hℓti]
        simp only [ht, ite_false]
        have h := hratio t
        simp only [ht, ite_false, mul_one] at h
        have := hpair t
        have hexp : exp (-η) * exp η = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
        have he : 7 / 3 ≤ exp η :=
          (by linarith [Real.exp_one_gt_d9] : (7 / 3 : ℝ) ≤ exp 1).trans (exp_le_exp.mpr hη)
        -- `a t i₂ = e^η a t i₁`
        have h' : a t i₂ = exp η * a t i₁ := by
          rw [h, ← mul_assoc, mul_comm (exp η), hexp, one_mul]
        rw [Pi.single_eq_of_ne h12]
        have hpos := softmax_pos (fun j ↦ -(η * ∑ s ∈ range t, ℓ s j)) i₁
        nlinarith
    have hsum : ∑ t ∈ range T, (if Even t then (1 / 2 : ℝ) else -(3 / 10)) =
        T / 10 + 2 / 5 * if Even T then 0 else 1 := by
      rw [← sum_range_ite_even, mul_sum]
      have : ∀ t : ℕ, (if Even t then (1 / 2 : ℝ) else -(3 / 10)) =
          1 / 10 + 2 / 5 * if Even t then 1 else -1 := fun t ↦ by split_ifs <;> norm_num
      simp_rw [this, sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
      ring
    calc (T : ℝ) / 10 ≤ T / 10 + 2 / 5 * if Even T then 0 else 1 := by split_ifs <;> norm_num
      _ = ∑ t ∈ range T, (if Even t then (1 / 2 : ℝ) else -(3 / 10)) := hsum.symm
      _ ≤ _ := sum_le_sum hround

/-- **The negative entropy needs exponentially small errors** [SSKM26, Theorem 4], with explicit
constants. Let the simplex have at least two arms, `η > 0`, and `ε ≥ 4 η e^{-η T / 3}`. There are
losses in `[0, 1]^d`, an `ε`-approximate trajectory `a` of mirror descent on the simplex with the
negative entropy and learning rate `η`, started at the uniform point and with positive
coordinates, and a best point `u` of the simplex in hindsight, such that the regret of `a` against
`u` after `T` rounds is at least `T / 10`. -/
theorem exists_approxMirrorDescent_le_regret_negEntropy (h2 : 2 ≤ Fintype.card α) {η ε : ℝ}
    (hη : 0 < η) (T : ℕ) (hε : 4 * η * exp (-(η * T / 3)) ≤ ε) :
    ∃ ℓ : ℕ → α → ℝ, (∀ t i, ℓ t i ∈ Set.Icc 0 1) ∧
    ∃ a : ℕ → α → ℝ, a 0 = (fun _ ↦ (Fintype.card α : ℝ)⁻¹) ∧ (∀ t i, 0 < a t i) ∧
      (∀ t < T, IsApproxMirrorDescentStep (simplex α) negEntropy η
        (∑ i, ℓ t i • ContinuousLinearMap.proj i) (a t)
        (∑ i, log (a t i) • ContinuousLinearMap.proj i) ε (a (t + 1))) ∧
    ∃ u ∈ simplex α, (∀ v ∈ simplex α,
        ∑ t ∈ range T, ∑ i, ℓ t i * u i ≤ ∑ t ∈ range T, ∑ i, ℓ t i * v i) ∧
      (T : ℝ) / 10 ≤ regret (fun t w ↦ ∑ i, ℓ t i * w i) a u T := by
  classical
  rcases le_or_gt η 1 with hη1 | hη1
  · -- `η ≤ 1`: Lemma 14 of [SSKM26] with `A = T / 3`
    obtain ⟨i₁⟩ : Nonempty α := Fintype.card_pos_iff.mp (by omega)
    have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    obtain ⟨ℓ, hℓ, hbest, -, a, ha0, hpos, hstep, hreg⟩ :=
      exists_approxMirrorDescent_le_regret_of_balanced h2 i₁ hη hη1 T (A := T / 3)
        (by positivity) (by linarith)
    refine ⟨ℓ, hℓ, a, ha0, hpos, hstep ε (by convert hε using 4; ring), Pi.single i₁ 1,
      single_mem_simplex i₁, fun v hv ↦ sum_sum_mul_single_le hbest hv, ?_⟩
    linarith
  · -- `η > 1`: exact steps on alternating losses
    exact exists_mirrorDescent_le_regret_negEntropy_of_one_le h2 hη1.le T
      (le_trans (by positivity) hε)

end Schlisselberg2026Hidden
