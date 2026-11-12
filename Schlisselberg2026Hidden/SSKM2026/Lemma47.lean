/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.SSKM2026.Lemma48
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Lemmas 46 and 47 of [SSKM26]: the trajectory of Theorem 8 is stuck

The trajectory `PolytopeLower.traj` of Theorem 8 of [SSKM26] stays at `W(e^{η n}, q_n)`. During
the first `τ` rounds it takes exact steps, so `q_n = f_n⁻¹(η G_n)` with `G_n = ∑_{s<n} S(ℓ s)`
(the instance of Lemma 10 of [SSKM26]). The paper's Lemma 47 bounds `q_τ` when `G_τ ≤ 0`; its
inequalities are inverted (`notes/paper-errata.md`, E32). We prove the sharpened form
`f_n⁻¹(γ) ≤ (2 / d) (2 / ρ_n)^m e^γ`, `ρ_n = 3 e^{η n} / (e^{η n} + 3)`, which tolerates
`η G_τ = O(1)`: on the median event `{G_τ ≤ τ μ}`, `q_τ ≤ (2 e^{7/2} / d) ε⁴`. From then on the
frozen steps are `ε`-approximate, so the trajectory keeps `q_n = q_τ ≤ 1 / d`. During the exact
phase, `q_n ≤ 1 / d` on `{G_n ≤ n μ}`, since `f_n(1 / d) ≥ η n μ` (the paper's Lemma 46 is the
bound `x_n(q) ≥ ρ_n / d` on the first coordinates, which this proof uses in the form
`curveY m E q ≥ (3 / d) / (E + 3)`).

## Main statements

* `PolytopeLower.trajQ_eq_levelInv`: [SSKM26, Lemma 10] for this instance: the exact phase is
  FTRL, `q_n = f_n⁻¹(η G_n)` for `n ≤ τ`.
* `PolytopeLower.levelInv_le`: [SSKM26, Lemma 47], corrected and sharpened.
* `PolytopeLower.trajQ_le_inv`: on `{G_{min(n, τ)} ≤ min(n, τ) μ}`, `q_n ≤ 1 / d`.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Real Set

namespace Schlisselberg2026Hidden.PolytopeLower

variable {m : ℕ} {η ε μ E q : ℝ} {τ : ℕ}

/-! ### Values at the uniform point -/

lemma curveY_one_inv : curveY m 1 (5 * m + 2 : ℝ)⁻¹ = (5 * m + 2 : ℝ)⁻¹ := by
  unfold curveY
  field_simp
  ring

lemma two_div_sub_inv : 2 / (5 * m + 2 : ℝ) - (5 * m + 2 : ℝ)⁻¹ = (5 * m + 2 : ℝ)⁻¹ := by
  field_simp
  ring

lemma inv_mem_Ioo : (5 * m + 2 : ℝ)⁻¹ ∈ Ioo 0 (2 / (5 * m + 2) : ℝ) := by
  have hd : (0 : ℝ) < 5 * m + 2 := by positivity
  refine ⟨inv_pos.mpr hd, ?_⟩
  rw [div_eq_mul_inv]
  linarith [inv_pos.mpr hd]

/-- The level of the uniform point at the start is `0`. -/
lemma level_one_inv : level m 1 (5 * m + 2 : ℝ)⁻¹ = 0 := by
  rw [level, curveY_one_inv, two_div_sub_inv, one_mul]
  ring

/-- The level of the point `q = 1 / d` is `m log (4 E / (E + 3))`. -/
lemma level_inv (hE : 0 < E) :
    level m E (5 * m + 2 : ℝ)⁻¹ = m * log (4 * E / (E + 3)) := by
  have hd : (0 : ℝ) < 5 * m + 2 := by positivity
  have hy : E * curveY m E (5 * m + 2 : ℝ)⁻¹ = (4 * E / (E + 3)) * (5 * m + 2 : ℝ)⁻¹ := by
    unfold curveY
    field_simp
    ring
  rw [level, two_div_sub_inv, hy, log_mul (by positivity) (by positivity)]
  ring

/-! ### The exact phase -/

/-- **The exact phase is FTRL** [SSKM26, Lemma 10], for this instance, with the corrected range
of the losses (erratum E9): for `n ≤ τ`, `q_n = f_n⁻¹(η G_n)`, `G_n = ∑_{s<n} S(ℓ s)`. -/
lemma trajQ_eq_levelInv (ℓ : ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ) {n : ℕ} (hn : n ≤ τ) :
    trajQ m η ε τ n ℓ =
      levelInv m (exp (η * n)) (η * ∑ s ∈ Finset.range n, lossZP (ℓ s)) := by
  induction n with
  | zero =>
    simp only [trajQ_zero, CharP.cast_eq_zero, mul_zero, exp_zero, Finset.range_zero,
      Finset.sum_empty]
    rw [← level_one_inv (m := m), levelInv_level one_pos inv_mem_Ioo]
  | succ n ih =>
    rw [trajQ_succ, ite_eq_right (by omega), ih (by omega), level_levelInv (exp_pos _),
      Finset.sum_range_succ, mul_add]

/-- **The first coordinates are high** [SSKM26, Lemma 46], in the form used here:
`y = curveY m E q ≥ (3 / d) / (E + 3)`. -/
lemma curveY_ge (hE : 0 < E) (hq : 0 ≤ q) :
    3 / (5 * m + 2) / (E + 3) ≤ curveY m E q := by
  unfold curveY
  gcongr
  linarith

/-- **The stuck base** [SSKM26, Lemma 47], corrected and sharpened:
`f(E, ·)⁻¹(γ) ≤ (2 / d) (2 / ρ)^m e^γ` with `ρ = 3 E / (E + 3)`. -/
lemma levelInv_le (hE : 0 < E) (γ : ℝ) :
    levelInv m E γ ≤ 2 / (5 * m + 2) * (2 / (3 * E / (E + 3))) ^ m * exp γ := by
  have hd : (0 : ℝ) < 5 * m + 2 := by positivity
  set q := levelInv m E γ
  have hq := levelInv_mem (m := m) hE γ
  have hγ : level m E q = γ := level_levelInv hE γ
  have hρ : 0 < 3 * E / (E + 3) := by positivity
  have hx : 3 * E / (E + 3) / (5 * m + 2) ≤ E * curveY m E q := by
    calc 3 * E / (E + 3) / (5 * m + 2) = E * (3 / (5 * m + 2) / (E + 3)) := by
          field_simp
      _ ≤ E * curveY m E q := by gcongr; exact curveY_ge hE hq.1.le
  have h1 : log (3 * E / (E + 3) / (5 * m + 2)) ≤ log (E * curveY m E q) :=
    log_le_log (by positivity) hx
  have h2 : log (2 / (5 * m + 2) - q) ≤ log (2 / (5 * m + 2)) :=
    log_le_log (sub_pos.mpr hq.2) (by linarith [hq.1])
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hlog : log q ≤ log (2 / (5 * m + 2) * (2 / (3 * E / (E + 3))) ^ m * exp γ) := by
    rw [log_mul (by positivity) (exp_pos _).ne', log_mul (by positivity) (by positivity),
      log_pow, log_exp, log_div (x := 2) two_ne_zero hρ.ne',
      log_div (x := 2) two_ne_zero hd.ne']
    rw [log_div hρ.ne' hd.ne'] at h1
    rw [log_div (x := 2) two_ne_zero hd.ne'] at h2
    rw [← hγ, level]
    nlinarith [mul_le_mul_of_nonneg_left h1 hm,
      mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ m + 1)]
  exact (log_le_log_iff hq.1 (by positivity)).mp hlog

/-- **The exact phase stays on the losing side** [SSKM26, proof of Theorem 49], corrected:
`f(e^u, 1 / d) ≥ u μ` for `0 ≤ u ≤ 4`, `μ ≤ 1` and `m ≥ 7`. -/
lemma mul_le_level_inv {u : ℝ} (hm : 7 ≤ m) (hu : 0 ≤ u) (hu4 : u ≤ 4) (hμ : μ ≤ 1) :
    u * μ ≤ level m (exp u) (5 * m + 2 : ℝ)⁻¹ := by
  rw [level_inv (exp_pos u)]
  set E := exp u
  have hE : 1 + u ≤ E := by linarith [add_one_le_exp u]
  have hE0 : 0 < E := exp_pos u
  have hlog := one_sub_inv_le_log_of_pos (show 0 < 4 * E / (E + 3) by positivity)
  rw [inv_div] at hlog
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have key : u ≤ m * (1 - (E + 3) / (4 * E)) := by
    rw [show (1 : ℝ) - (E + 3) / (4 * E) = 3 * (E - 1) / (4 * E) by field_simp; ring,
      mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  calc u * μ ≤ u := by nlinarith
    _ ≤ m * (1 - (E + 3) / (4 * E)) := key
    _ ≤ m * log (4 * E / (E + 3)) := by gcongr

/-! ### The frozen phase -/

/-- Along the curve, one round moves the level of a fixed `q` by `m log (x_{n+1}(q) / x_n(q))`,
between `0` and `m η`. -/
lemma level_exp_mul_sub_level (hE : 0 < E) (hη : 0 ≤ η) (hq : 0 < q) :
    0 ≤ level m (exp η * E) q - level m E q ∧ level m (exp η * E) q - level m E q ≤ m * η := by
  have hE' : 0 < exp η * E := mul_pos (exp_pos η) hE
  have hc : (0 : ℝ) < 3 / (5 * m + 2) + q := by positivity
  have e1 : log (exp η * E * ((3 / (5 * m + 2) + q) / (exp η * E + 3))) =
      η + log E + log (3 / (5 * m + 2) + q) - log (exp η * E + 3) := by
    rw [log_mul hE'.ne' (by positivity), log_mul (exp_pos η).ne' hE.ne', log_exp,
      log_div hc.ne' (by positivity)]
    ring
  have e2 : log (E * ((3 / (5 * m + 2) + q) / (E + 3))) =
      log E + log (3 / (5 * m + 2) + q) - log (E + 3) := by
    rw [log_mul hE.ne' (by positivity), log_div hc.ne' (by positivity)]
    ring
  have hdiff : level m (exp η * E) q - level m E q =
      m * (η - (log (exp η * E + 3) - log (E + 3))) := by
    unfold level curveY
    rw [e1, e2]
    ring
  have h1 : log (E + 3) ≤ log (exp η * E + 3) := by
    have : E ≤ exp η * E := le_mul_of_one_le_left hE.le (one_le_exp hη)
    exact log_le_log (by positivity) (by linarith)
  have h2 : log (exp η * E + 3) ≤ η + log (E + 3) := by
    rw [← log_exp η, ← log_mul (exp_pos η).ne' (by positivity), log_exp]
    exact log_le_log (by positivity) (by nlinarith [one_le_exp hη])
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [hdiff]
  constructor <;> nlinarith

/-- **The frozen phase**: if every loss has `|S(ℓ t)| ≤ m + 1`, `η (2 m + 1) ≤ 1` and
`3 q_τ ≤ ε`, then every step from round `τ` on is frozen: `q_n = q_τ` for `n ≥ τ`. -/
lemma trajQ_eq_trajQ_of_le (hη : 0 ≤ η) (hηm : η * (2 * m + 1) ≤ 1)
    {ℓ : ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ} (hS : ∀ t, |lossZP (ℓ t)| ≤ m + 1)
    (hq : 3 * trajQ m η ε τ τ ℓ ≤ ε) {n : ℕ} (hn : τ ≤ n) :
    trajQ m η ε τ n ℓ = trajQ m η ε τ τ ℓ := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [trajQ_succ, ite_eq_left, ih]
    refine ⟨hn, ?_⟩
    rw [ih]
    have hq0 := (trajQ_mem (η := η) (ε := ε) (τ := τ) τ ℓ).1
    obtain ⟨h1, h2⟩ := level_exp_mul_sub_level (m := m) (exp_pos (η * n)) hη hq0
    rw [← exp_mul_succ] at h1 h2
    have hSn := abs_le.mp (hS n)
    have hr : |level m (exp (η * ↑(n + 1))) (trajQ m η ε τ τ ℓ) -
        level m (exp (η * n)) (trajQ m η ε τ τ ℓ) - η * lossZP (ℓ n)| ≤ 1 := by
      rw [abs_le]
      constructor <;> nlinarith
    calc trajQ m η ε τ τ ℓ * expRem _ ≤ trajQ m η ε τ τ ℓ * 3 :=
          mul_le_mul_of_nonneg_left (expRem_le_three hr) hq0.le
      _ ≤ ε := by linarith

/-! ### Numerical bounds -/

lemma exp_three_ge : 20 ≤ exp 3 := by
  have h := exp_one_gt_d9
  calc (20 : ℝ) ≤ 2.7182818283 ^ 3 := by norm_num
    _ ≤ exp 1 ^ 3 := by gcongr
    _ = exp 3 := by rw [← exp_nat_mul]; norm_num

lemma exp_seven_halves_le : exp (7 / 2) ≤ 34 := by
  have h := exp_one_lt_d9
  have h7 : exp (7 / 2) ^ 2 ≤ 34 ^ 2 := by
    calc exp (7 / 2) ^ 2 = exp 1 ^ 7 := by rw [← exp_nat_mul, ← exp_nat_mul]; norm_num
      _ ≤ 2.7182818286 ^ 7 := by gcongr
      _ ≤ 34 ^ 2 := by norm_num
  exact (pow_le_pow_iff_left₀ (exp_pos _).le (by norm_num) (by norm_num)).mp h7

lemma le_exp_neg_quarter : (23 / 30 : ℝ) ≤ exp (-(1 / 4)) := by
  rw [exp_neg, le_inv_comm₀ (by norm_num) (exp_pos _)]
  have h := exp_one_lt_d9
  have h4 : exp (1 / 4) ^ 4 ≤ (30 / 23) ^ 4 := by
    calc exp (1 / 4) ^ 4 = exp 1 := by rw [← exp_nat_mul]; norm_num
      _ ≤ 2.7182818286 := h.le
      _ ≤ (30 / 23) ^ 4 := by norm_num
  have := (pow_le_pow_iff_left₀ (exp_pos _).le (by norm_num) (by norm_num)).mp h4
  simpa using this

/-- With `E ≥ e³` and `m ≥ 16 log (1 / ε)`, `(2 / ρ)^m ≤ ε⁴`. -/
lemma two_div_rho_pow_le (hε : 0 < ε) (hm : 16 * log (1 / ε) ≤ m) (hE : exp 3 ≤ E) :
    (2 / (3 * E / (E + 3))) ^ m ≤ ε ^ 4 := by
  have hE0 : 0 < E := (exp_pos 3).trans_le hE
  have h20 : 20 ≤ E := exp_three_ge.trans hE
  have hρ : 2 / (3 * E / (E + 3)) ≤ 23 / 30 := by
    rw [div_le_iff₀ (by positivity)]
    rw [show 23 / 30 * (3 * E / (E + 3)) = 23 * E / (10 * (E + 3)) by field_simp; ring,
      le_div_iff₀ (by positivity)]
    linarith
  calc (2 / (3 * E / (E + 3))) ^ m ≤ exp (-(1 / 4)) ^ m := by
        gcongr
        exact hρ.trans le_exp_neg_quarter
    _ = exp (-(m / 4)) := by rw [← exp_nat_mul]; ring_nf
    _ ≤ exp (4 * log ε) := by
        gcongr
        rw [one_div, log_inv] at hm
        linarith
    _ = ε ^ 4 := by
        rw [show (4 : ℝ) * log ε = ((4 : ℕ) : ℝ) * log ε by norm_num, ← log_pow,
          exp_log (by positivity)]

/-! ### The trajectory is stuck -/

/-- **The trajectory of Theorem 8 is stuck** [SSKM26, Lemmas 45–47], corrected: under the
parameter constraints of the construction (`ε ≤ 1 / 3`, `m ≥ max(7, 16 log (1 / ε))`,
`η d ≤ 1`, `3 ≤ η τ ≤ 7 / 2`, `μ ≤ 1`), for losses with `|S(ℓ t)| ≤ m + 1`, if
`G_k ≤ k μ` for `k = min(n, τ)` then `q_n ≤ 1 / d`. -/
lemma trajQ_le_inv (hη : 0 < η) (hηd : η * (5 * m + 2) ≤ 1) (hm7 : 7 ≤ m) (hε : 0 < ε)
    (hε3 : ε ≤ 1 / 3) (hm : 16 * log (1 / ε) ≤ m) (hτ : 3 ≤ η * τ) (hτ' : η * τ ≤ 7 / 2)
    (hμ1 : μ ≤ 1) {ℓ : ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ}
    (hS : ∀ t, |lossZP (ℓ t)| ≤ m + 1) (n : ℕ)
    (hG : ∑ s ∈ Finset.range (min n τ), lossZP (ℓ s) ≤ min n τ * μ) :
    trajQ m η ε τ n ℓ ≤ (5 * m + 2 : ℝ)⁻¹ := by
  have hd : (0 : ℝ) < 5 * m + 2 := by positivity
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm7
  rcases le_or_gt n τ with hnτ | hnτ
  · -- the exact phase
    rw [min_eq_left hnτ] at hG
    rw [trajQ_eq_levelInv ℓ hnτ]
    have hn : η * n ≤ 7 / 2 := le_trans (by gcongr) hτ'
    calc levelInv m (exp (η * n)) (η * ∑ s ∈ Finset.range n, lossZP (ℓ s))
        ≤ levelInv m (exp (η * n)) (level m (exp (η * n)) (5 * m + 2 : ℝ)⁻¹) := by
          refine monotone_levelInv (exp_pos _) ?_
          calc η * ∑ s ∈ Finset.range n, lossZP (ℓ s) ≤ η * (n * μ) := by gcongr
            _ = η * n * μ := by ring
            _ ≤ _ := mul_le_level_inv hm7 (by positivity) (by linarith) hμ1
      _ = (5 * m + 2 : ℝ)⁻¹ := levelInv_level (exp_pos _) inv_mem_Ioo
  · -- the frozen phase
    rw [min_eq_right hnτ.le] at hG
    have hqτ : trajQ m η ε τ τ ℓ ≤ 2 / (5 * m + 2) * ε ^ 4 * 34 := by
      rw [trajQ_eq_levelInv ℓ le_rfl]
      refine (levelInv_le (exp_pos _) _).trans ?_
      have h1 : (2 / (3 * exp (η * τ) / (exp (η * τ) + 3))) ^ m ≤ ε ^ 4 :=
        two_div_rho_pow_le hε hm (exp_le_exp.mpr hτ)
      have h2 : exp (η * ∑ s ∈ Finset.range τ, lossZP (ℓ s)) ≤ 34 := by
        refine le_trans (exp_le_exp.mpr ?_) exp_seven_halves_le
        calc η * ∑ s ∈ Finset.range τ, lossZP (ℓ s) ≤ η * (τ * μ) := by gcongr
          _ ≤ η * τ := by rw [← mul_assoc]; nlinarith
          _ ≤ 7 / 2 := hτ'
      gcongr
    have hε4 : ε ^ 4 ≤ ε * (1 / 27) := by
      have : ε ^ 3 ≤ (1 / 3) ^ 3 := by gcongr
      nlinarith [pow_pos hε 3]
    have hq3 : 3 * trajQ m η ε τ τ ℓ ≤ ε := by
      have h37 : (37 : ℝ) ≤ 5 * m + 2 := by linarith
      calc 3 * trajQ m η ε τ τ ℓ ≤ 3 * (2 / (5 * m + 2) * ε ^ 4 * 34) := by gcongr
        _ ≤ 3 * (2 / 37 * (ε * (1 / 27)) * 34) := by gcongr
        _ ≤ ε := by nlinarith
    rw [trajQ_eq_trajQ_of_le hη.le (by nlinarith) hS hq3 hnτ.le]
    calc trajQ m η ε τ τ ℓ ≤ 2 / (5 * m + 2) * ε ^ 4 * 34 := hqτ
      _ ≤ 2 / (5 * m + 2) * (1 / 81) * 34 := by
          gcongr
          calc ε ^ 4 ≤ (1 / 3) ^ 4 := by gcongr
            _ = 1 / 81 := by norm_num
      _ ≤ (5 * m + 2 : ℝ)⁻¹ := by
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, inv_eq_one_div,
            div_le_div_iff_of_pos_right hd]
          norm_num

end Schlisselberg2026Hidden.PolytopeLower
