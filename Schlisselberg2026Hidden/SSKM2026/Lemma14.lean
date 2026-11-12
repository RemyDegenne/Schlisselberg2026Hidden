/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent
public import LMLExplore.Analysis.Convex.NegEntropy
public import Schlisselberg2026Hidden.SSKM2026.Lemma34

/-!
# Lemma 14 of [SSKM26]: balanced losses with linear regret for the negative entropy

On the simplex with at least two arms and the negative entropy, for `0 < η ≤ 1` and
`0 ≤ A ≤ T / 2`, there are `A`-balanced losses in `[0, 1]^d` and a trajectory started at the
uniform point that is `ε`-approximate for every `ε ≥ 4 η e^{-η A}` and has regret at least
`(T - 2 A) / 2` against the best arm `i₁`. The losses put loss `1` on `i₁` for `⌊A⌋` rounds, so
that its weight under exact steps falls to about `e^{-η A}`, and then loss `1` on all the other
arms; from then on, staying put is an `ε`-approximate step.

The paper states the lemma for two arms, chooses the losses after `ε` in its proof, gives the
regret `Ω(T - 2α)` (its accounting gives `(T - 3τ) / 2`), and has no condition on `η`; the
construction needs `η ≤ 1` (`notes/paper-errata.md`).

## Main statements

* `Schlisselberg2026Hidden.exists_approxMirrorDescent_le_regret_of_balanced`:
  [SSKM26, Lemma 14], corrected.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The weight of the distinguished coordinate in the exponential weights of a vector that vanishes
off it: `softmax (x e_{i₁}) i₁ = e^x / (e^x + d - 1)`. -/
lemma softmax_ite_apply_self (i₁ : α) (x : ℝ) :
    softmax (fun j ↦ if j = i₁ then x else 0) i₁ = exp x / (exp x + (Fintype.card α - 1)) := by
  rw [softmax_apply, sum_eq_add_mul_of_forall_ne (f := fun j ↦ exp (if j = i₁ then x else 0))
    (i₀ := i₁) (c := 1) fun j hj ↦ by simp [hj]]
  simp

/-- The weight of the distinguished coordinate in the exponential weights of a vector that vanishes
off it is at most `e^x`, in dimension at least `2`. -/
lemma softmax_ite_apply_self_le (h2 : 2 ≤ Fintype.card α) (i₁ : α) (x : ℝ) :
    softmax (fun j ↦ if j = i₁ then x else 0) i₁ ≤ exp x := by
  rw [softmax_ite_apply_self]
  have hd : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast h2
  exact div_le_self (exp_pos x).le (by linarith [exp_pos x])

/-- The weight of the distinguished coordinate in the exponential weights of a vector that vanishes
off it is monotone in its value there. -/
lemma softmax_ite_apply_self_mono (h2 : 2 ≤ Fintype.card α) (i₁ : α) {x y : ℝ} (hxy : x ≤ y) :
    softmax (fun j ↦ if j = i₁ then x else 0) i₁ ≤
      softmax (fun j ↦ if j = i₁ then y else 0) i₁ := by
  rw [softmax_ite_apply_self, softmax_ite_apply_self]
  have hd : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast h2
  have hx := exp_pos x
  have hexp : exp x ≤ exp y := exp_le_exp.mpr hxy
  rw [div_le_div_iff₀ (by linarith) (by linarith [exp_pos y])]
  nlinarith

/-- A vertex `e_{i₁}` minimizes the cumulative loss over the simplex as soon as `i₁` minimizes it
over the coordinates. -/
lemma sum_sum_mul_single_le {ℓ : ℕ → α → ℝ} {T : ℕ} {i₁ : α}
    (h : ∀ i, ∑ t ∈ range T, ℓ t i₁ ≤ ∑ t ∈ range T, ℓ t i) {v : α → ℝ} (hv : v ∈ simplex α) :
    ∑ t ∈ range T, ∑ i, ℓ t i * (Pi.single i₁ 1 : α → ℝ) i ≤
      ∑ t ∈ range T, ∑ i, ℓ t i * v i := by
  have hl : ∀ t, ∑ i, ℓ t i * (Pi.single i₁ 1 : α → ℝ) i = ℓ t i₁ := fun t ↦ by
    simp [Pi.single_apply]
  have hv' := mem_simplex_iff.mp hv
  calc ∑ t ∈ range T, ∑ i, ℓ t i * (Pi.single i₁ 1 : α → ℝ) i
      = ∑ i, v i * ∑ t ∈ range T, ℓ t i₁ := by
        simp_rw [hl]
        rw [← Finset.sum_mul, hv'.2, one_mul]
    _ ≤ ∑ i, v i * ∑ t ∈ range T, ℓ t i :=
        Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (h i) (hv'.1 i)
    _ = ∑ t ∈ range T, ∑ i, ℓ t i * v i := by
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum, mul_comm]

/-- **Balanced losses with linear regret** [SSKM26, Lemma 14], corrected. Let the simplex have at
least two arms, let `i₁` be an arm, `0 < η ≤ 1`, and `0 ≤ A` with `2 A ≤ T`. There are losses in
`[0, 1]^d` for which `i₁` is a best arm over `T` rounds and which are `A`-balanced with respect to
`i₁`, and a trajectory `a` started at the uniform point with positive coordinates, such that for
every `ε ≥ 4 η e^{-η A}`, `a` is an `ε`-approximate trajectory of mirror descent on the simplex with
the negative entropy and learning rate `η`, and its regret against the vertex `i₁` is at least
`(T - 2 A) / 2`. The losses and the trajectory do not depend on `ε`. -/
theorem exists_approxMirrorDescent_le_regret_of_balanced (h2 : 2 ≤ Fintype.card α) (i₁ : α)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (T : ℕ) {A : ℝ} (hA : 0 ≤ A) (hAT : 2 * A ≤ T) :
    ∃ ℓ : ℕ → α → ℝ, (∀ t i, ℓ t i ∈ Set.Icc 0 1) ∧
      (∀ i, ∑ t ∈ range T, ℓ t i₁ ≤ ∑ t ∈ range T, ℓ t i) ∧
      (∀ s t, s ≤ t → t ≤ T → ∀ i, ∑ r ∈ Ico s t, (ℓ r i₁ - ℓ r i) ≤ A) ∧
    ∃ a : ℕ → α → ℝ, a 0 = (fun _ ↦ (Fintype.card α : ℝ)⁻¹) ∧ (∀ t i, 0 < a t i) ∧
      (∀ ε, 4 * η * exp (-(η * A)) ≤ ε → ∀ t < T,
        IsApproxMirrorDescentStep (simplex α) negEntropy η
          (∑ i, ℓ t i • ContinuousLinearMap.proj i) (a t)
          (∑ i, log (a t i) • ContinuousLinearMap.proj i) ε (a (t + 1))) ∧
      (T - 2 * A) / 2 ≤ regret (fun t w ↦ ∑ i, ℓ t i * w i) a (Pi.single i₁ 1) T := by
  have : Nonempty α := ⟨i₁⟩
  have hd2 : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast h2
  set τ := ⌊A⌋₊ with hτ_def
  have hτA : (τ : ℝ) ≤ A := Nat.floor_le hA
  have hAτ : A < τ + 1 := Nat.lt_floor_add_one A
  have hτT : 2 * τ ≤ T := by
    have : ((2 * τ : ℕ) : ℝ) ≤ T := by push_cast; linarith
    exact_mod_cast this
  have hτT' : τ ≤ T := by omega
  -- the losses: `e_{i₁}` for `t < τ`, then `1 - e_{i₁}`
  set ℓ : ℕ → α → ℝ := fun t j ↦
    if t < τ then (if j = i₁ then 1 else 0) else (if j = i₁ then 0 else 1) with hℓ_def
  -- the trajectory: `min t τ` exact steps from the uniform point
  set v : ℕ → α → ℝ := fun t j ↦ if j = i₁ then -(η * (min t τ : ℕ)) else 0 with hv_def
  set a : ℕ → α → ℝ := fun t ↦ softmax (v t) with ha_def
  have hasimp : ∀ t, ∑ i, a t i = 1 := fun t ↦ sum_softmax _
  have hai₁ : ∀ t, a t i₁ = softmax (fun j ↦ if j = i₁ then -(η * (min t τ : ℕ)) else 0) i₁ :=
    fun t ↦ rfl
  have hstay : ∀ t, τ ≤ t → a t = a τ := fun t ht ↦ by
    simp only [ha_def, hv_def, min_eq_right ht, min_self]
  set p := a τ i₁ with hp_def
  have hp_le : p ≤ exp (-(η * τ)) := by
    rw [hp_def, hai₁, min_self]
    exact softmax_ite_apply_self_le h2 i₁ _
  have hp_half : p ≤ 1 / 2 := by
    rw [hp_def, hai₁, min_self, softmax_ite_apply_self]
    have h1 : exp (-(η * (τ : ℝ))) ≤ 1 := exp_le_one_iff.mpr (by
      have : (0 : ℝ) ≤ τ := Nat.cast_nonneg τ
      nlinarith)
    rw [div_le_iff₀ (by linarith [exp_pos (-(η * (τ : ℝ)))])]
    linarith
  have hp_mono : ∀ t, t ≤ τ → p ≤ a t i₁ := fun t ht ↦ by
    rw [hp_def, hai₁, hai₁, min_self, min_eq_left ht]
    refine softmax_ite_apply_self_mono h2 i₁ ?_
    have : (t : ℝ) ≤ τ := by exact_mod_cast ht
    nlinarith
  refine ⟨ℓ, fun t i ↦ ?_, fun i ↦ ?_, fun s t hst htT i ↦ ?_, a, ?_, fun t i ↦ softmax_pos _ _,
    fun ε hε t ht ↦ ?_, ?_⟩
  · -- the losses lie in `[0, 1]`
    simp only [hℓ_def]
    split_ifs <;> simp
  · -- `i₁` is a best arm
    by_cases hi : i = i₁
    · rw [hi]
    rw [← sum_range_add_sum_Ico _ hτT', ← sum_range_add_sum_Ico _ hτT']
    have h1 : ∀ t ∈ range τ, ℓ t i₁ = 1 := fun t ht ↦ by simp [hℓ_def, mem_range.mp ht]
    have h2 : ∀ t ∈ Ico τ T, ℓ t i₁ = 0 := fun t ht ↦ by
      simp [hℓ_def, not_lt.mpr (mem_Ico.mp ht).1]
    have h3 : ∀ t ∈ range τ, ℓ t i = 0 := fun t ht ↦ by simp [hℓ_def, mem_range.mp ht, hi]
    have h4 : ∀ t ∈ Ico τ T, ℓ t i = 1 := fun t ht ↦ by
      simp [hℓ_def, not_lt.mpr (mem_Ico.mp ht).1, hi]
    rw [sum_congr rfl h1, sum_congr rfl h2, sum_congr rfl h3, sum_congr rfl h4]
    simp only [sum_const, card_range, Nat.card_Ico, nsmul_eq_mul, mul_one, mul_zero, add_zero,
      zero_add]
    rw [Nat.cast_sub hτT']
    have : ((2 * τ : ℕ) : ℝ) ≤ T := by exact_mod_cast hτT
    push_cast at this
    linarith
  · -- the losses are `A`-balanced
    by_cases hi : i = i₁
    · simp [hi, hA]
    calc ∑ r ∈ Ico s t, (ℓ r i₁ - ℓ r i) ≤ ∑ r ∈ Ico s t, (if r < τ then (1 : ℝ) else 0) :=
          sum_le_sum fun r _ ↦ by by_cases hr : r < τ <;> simp [hℓ_def, hr, hi]
      _ = (((Ico s t).filter (· < τ)).card : ℝ) := by rw [sum_boole]
      _ ≤ ((range τ).card : ℝ) := by
          exact_mod_cast card_le_card fun r hr ↦ by
            simp only [mem_filter] at hr
            exact mem_range.mpr hr.2
      _ = τ := by simp
      _ ≤ A := hτA
  · -- the trajectory starts at the uniform point
    rw [← softmax_zero]
    simp only [ha_def, hv_def]
    congr 1
    funext j
    simp
  · -- the steps are approximate
    have hε0 : 0 ≤ ε := le_trans (by positivity) hε
    by_cases htτ : t < τ
    · -- an exact step
      have hstep : IsMirrorDescentStep (simplex α) negEntropy η
          (∑ i, ℓ t i • ContinuousLinearMap.proj i) (a t)
          (∑ i, log (a t i) • ContinuousLinearMap.proj i) (a (t + 1)) := by
        rw [isMirrorDescentStep_negEntropy_iff (softmax_mem_simplex _) (softmax_pos _)]
        simp only [ha_def]
        simp_rw [sub_eq_add_neg, softmax_log_softmax_add]
        congr 1
        funext j
        simp only [hv_def, hℓ_def, htτ, ite_true]
        rw [min_eq_left htτ.le, min_eq_left (by omega : t + 1 ≤ τ)]
        split_ifs <;> push_cast <;> ring
      exact hstep.isApproxMirrorDescentStep.mono hε0
    · -- staying put
      rw [not_lt] at htτ
      rw [hstay (t + 1) (by omega), hstay t htτ]
      refine isApproxMirrorDescentStep_negEntropy_self (softmax_mem_simplex _) (softmax_pos _)
        (i₀ := i₁) (by simp [hℓ_def, not_lt.mpr htτ])
        (fun j hj ↦ by simp [hℓ_def, not_lt.mpr htτ, hj]) hη.le hη1 ?_
      refine le_trans ?_ hε
      have h1 : exp (-(η * τ)) ≤ exp η * exp (-(η * A)) := by
        rw [← exp_add]
        exact exp_le_exp.mpr (by nlinarith)
      have h2 : exp η ≤ 3 := (exp_le_exp.mpr hη1).trans (by linarith [Real.exp_one_lt_d9])
      have h3 : η ^ 2 ≤ η := by nlinarith
      calc η ^ 2 * min (a τ i₁) (1 - a τ i₁) ≤ η ^ 2 * p :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) (sq_nonneg _)
        _ ≤ η * (3 * exp (-(η * A))) :=
            mul_le_mul h3 (hp_le.trans (h1.trans (mul_le_mul_of_nonneg_right h2 (exp_pos _).le)))
              (softmax_pos _ _).le hη.le
        _ ≤ 4 * η * exp (-(η * A)) := by nlinarith [exp_pos (-(η * A))]
  · -- the regret
    rw [regret_eq_sum_sub_sum, ← sum_sub_distrib, ← sum_range_add_sum_Ico _ hτT']
    have hsingle : ∑ i, (Pi.single i₁ 1 : α → ℝ) i = 1 := by simp
    have h1 : ∀ t ∈ range τ, p - 1 ≤
        ∑ i, ℓ t i * a t i - ∑ i, ℓ t i * (Pi.single i₁ 1 : α → ℝ) i := fun t ht ↦ by
      have htτ := mem_range.mp ht
      have hℓt : ∀ j ≠ i₁, ℓ t j = 0 := fun j hj ↦ by simp [hℓ_def, htτ, hj]
      have hℓti : ℓ t i₁ = 1 := by simp [hℓ_def, htτ]
      rw [sum_mul_eq_add_mul_of_forall_ne (hasimp t) hℓt,
        sum_mul_eq_add_mul_of_forall_ne hsingle hℓt, hℓti]
      simp only [Pi.single_eq_same]
      linarith [hp_mono t htτ.le]
    have h2 : ∀ t ∈ Ico τ T,
        ∑ i, ℓ t i * a t i - ∑ i, ℓ t i * (Pi.single i₁ 1 : α → ℝ) i = 1 - p := fun t ht ↦ by
      have htτ := (mem_Ico.mp ht).1
      have hℓt : ∀ j ≠ i₁, ℓ t j = 1 := fun j hj ↦ by simp [hℓ_def, not_lt.mpr htτ, hj]
      have hℓti : ℓ t i₁ = 0 := by simp [hℓ_def, not_lt.mpr htτ]
      rw [sum_mul_eq_add_mul_of_forall_ne (hasimp t) hℓt,
        sum_mul_eq_add_mul_of_forall_ne hsingle hℓt, hℓti, hstay t htτ]
      simp only [Pi.single_eq_same]
      ring
    have hs1 := sum_le_sum h1
    rw [sum_congr rfl h2]
    simp only [sum_const, card_range, Nat.card_Ico, nsmul_eq_mul] at hs1 ⊢
    rw [Nat.cast_sub hτT']
    have hT2 : ((2 * τ : ℕ) : ℝ) ≤ T := by exact_mod_cast hτT
    push_cast at hT2
    nlinarith

end Schlisselberg2026Hidden
