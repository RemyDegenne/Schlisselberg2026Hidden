/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent
public import Schlisselberg2026Hidden.SSKM2026.EntropyUpper.IidBalanced
public import Schlisselberg2026Hidden.SSKM2026.Lemma15
public import LMLExplore.Analysis.Convex.NegEntropy
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic

/-!
# Theorem 7 of [SSKM26]: stochastic losses make the negative entropy robust

On the simplex with the negative entropy, for i.i.d. losses in `[-1, 1]^d`, the uniform initial
point, `η = √(log d / T)` with `T ≥ 256 log d`, and `ε ≤ δ / (6 d³ T⁴)`, with probability at
least `1 - δ` every `ε`-approximate trajectory of mirror descent has regret at most
`2 √(T log d)`: polynomially small errors suffice, unlike for adversarial losses (Theorem 4 of
[SSKM26]).

With probability at least `1 - δ`, the i.i.d. losses are `√(2 T log (d² (T + 1)² / δ))`-balanced
(a sub-Gaussian bound for the bridges `L_{[s,t)}(i) - L_{[s,t)}(j) - (t - s)/T L_{[0,T)}(i) +
(t - s)/T L_{[0,T)}(j)`, which handles the random best arm), and Lemma 15 of [SSKM26] applies.

The paper states the theorem with `T ≥ 256`, `ε ≤ δ / (6 d² T⁴)` and `O(√(T log d))`; its proof
needs `η ≤ 1/16`, that is `T ≥ 256 log d`, and does not give the factor `d²`
(`notes/paper-errata.md`).

## Main statements

* `Schlisselberg2026Hidden.approxMirrorDescent_regret_le_negEntropy_iid`: [SSKM26, Theorem 7],
  corrected.
* `Schlisselberg2026Hidden.div_le_exp_neg_mul_min_div`: [SSKM26, proof of Theorem 7], the
  threshold on the error, corrected.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real MeasureTheory ProbabilityTheory

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α] {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The threshold of Theorem 7** [SSKM26, proof of Theorem 7], with corrected constants. For
`d ≥ 2` arms, `T ≥ 256 log d`, `0 < δ ≤ 1`, the learning rate `η = √(log d / T)` and the balance
`A = √(2 T log (d² (T + 1)² / δ))` of i.i.d. losses, the error `δ / (6 d³ T⁴)` is at most
the threshold `e^{-η A} min (η⁴, 1/T²) / (100 d)` of Lemma 15 of [SSKM26]. -/
lemma div_le_exp_neg_mul_min_div {d T δ : ℝ} (hd : 2 ≤ d) (hT : 256 * log d ≤ T) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    δ / (6 * d ^ 3 * T ^ 4) ≤ exp (-(√(log d / T) * √(2 * T * log (d ^ 2 * (T + 1) ^ 2 / δ)))) *
      min (√(log d / T) ^ 4) (1 / T ^ 2) / (100 * d) := by
  have hlog2 := log_two_gt_d9
  have hlogd : log 2 ≤ log d := log_le_log two_pos hd
  have hL : 0 < log d := by linarith
  have hT177 : 177 < T := by linarith
  have hT0 : 0 < T := by linarith
  have hd0 : 0 < d := by linarith
  set η := √(log d / T) with hη_def
  set N : ℝ := d ^ 2 * (T + 1) ^ 2 with hN_def
  set A := √(2 * T * log (N / δ)) with hA_def
  have hη : 0 < η := sqrt_pos.2 (div_pos hL hT0)
  have hη2 : η ^ 2 = log d / T := sq_sqrt (div_pos hL hT0).le
  have hN1 : 1 ≤ N :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ (by linarith))
  have hlogN : 0 ≤ log (N / δ) := log_nonneg ((one_le_div hδ).2 (hδ1.trans hN1))
  -- `η A ≤ log d + log (N / δ) / 2`, by the inequality of arithmetic and geometric means
  have hηA : η * A ≤ log d + log (N / δ) / 2 := by
    have hsq : (η * A) ^ 2 = 2 * log d * log (N / δ) := by
      rw [mul_pow, hη2, hA_def, sq_sqrt (by positivity)]
      field_simp
    have h2 : (η * A) ^ 2 ≤ (log d + log (N / δ) / 2) ^ 2 := by
      rw [hsq]
      nlinarith [sq_nonneg (log d - log (N / δ) / 2)]
    exact (pow_le_pow_iff_left₀ (mul_nonneg hη.le (sqrt_nonneg _)) (by positivity)
      two_ne_zero).1 h2
  -- hence `δ ≤ e^{-η A} d² (T + 1)`
  set X := exp (-(η * A)) with hX_def
  have hX0 : 0 < X := exp_pos _
  have hW : δ ≤ X * d ^ 2 * (T + 1) := by
    have h2 : 2 * (η * A) ≤ log (d ^ 2 * N / δ) := by
      rw [mul_div_assoc, log_mul (by positivity) (by positivity), log_pow]
      push_cast
      linarith
    have h3 : δ / (d ^ 2 * N) ≤ X ^ 2 := by
      calc δ / (d ^ 2 * N) = exp (-log (d ^ 2 * N / δ)) := by
            rw [exp_neg, exp_log (by positivity), inv_div]
        _ ≤ exp (2 * -(η * A)) := exp_le_exp.2 (by linarith)
        _ = X ^ 2 := by rw [hX_def, ← exp_nat_mul]; norm_num
    have h4 : δ ≤ (X * d ^ 2 * (T + 1)) ^ 2 := by
      rw [div_le_iff₀ (by positivity)] at h3
      calc δ ≤ X ^ 2 * (d ^ 2 * N) := h3
        _ = (X * d ^ 2 * (T + 1)) ^ 2 := by rw [hN_def]; ring
    by_contra h
    have h5 : (X * d ^ 2 * (T + 1)) ^ 2 < δ ^ 2 :=
      pow_lt_pow_left₀ (not_le.1 h) (by positivity) two_ne_zero
    have h6 : δ ^ 2 ≤ δ := by nlinarith
    linarith
  -- `min (η⁴, 1/T²) ≥ (log 2)² / T² ≥ 0.48 / T²`
  have hmin : 48 / 100 / T ^ 2 ≤ min (η ^ 4) (1 / T ^ 2) := by
    refine le_min ?_ (by gcongr; norm_num)
    rw [show η ^ 4 = (η ^ 2) ^ 2 by ring, hη2, div_pow]
    gcongr
    have := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 0.6931471803)
      (show 0.6931471803 ≤ log d by linarith)
    nlinarith
  calc δ / (6 * d ^ 3 * T ^ 4) ≤ X * (48 / 100 / T ^ 2) / (100 * d) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h3 : X * (48 / 100 / T ^ 2) * (6 * d ^ 3 * T ^ 4) =
            288 / 100 * (X * d ^ 2 * T ^ 2) * d := by
          field_simp
          norm_num
        rw [h3]
        have h0 : 0 ≤ X * d ^ 2 * T := by positivity
        have h1 : X * d ^ 2 * (T + 1) * T ≤ 2 * (X * d ^ 2 * T ^ 2) := by
          calc X * d ^ 2 * (T + 1) * T = (X * d ^ 2 * T) * (T + 1) := by ring
            _ ≤ (X * d ^ 2 * T) * (2 * T) := mul_le_mul_of_nonneg_left (by linarith) h0
            _ = 2 * (X * d ^ 2 * T ^ 2) := by ring
        have h2 : δ * T ≤ X * d ^ 2 * (T + 1) * T := mul_le_mul_of_nonneg_right hW hT0.le
        have h5 : 177 * δ ≤ δ * T := by nlinarith
        have h4 : 100 * δ ≤ 288 / 100 * (X * d ^ 2 * T ^ 2) := by linarith
        calc δ * (100 * d) = 100 * δ * d := by ring
          _ ≤ 288 / 100 * (X * d ^ 2 * T ^ 2) * d := mul_le_mul_of_nonneg_right h4 hd0.le
    _ ≤ X * min (η ^ 4) (1 / T ^ 2) / (100 * d) := by gcongr

/-- **Stochastic losses make the negative entropy robust** [SSKM26, Theorem 7], with corrected
constants. Let the losses `ℓ t` be independent and identically distributed over the rounds, with
coordinates in `[-1, 1]`, let `0 < δ ≤ 1`, `T ≥ 256 log d` with `d` the number of arms, and
`ε ≤ δ / (6 d³ T⁴)`. Then there is a measurable event of probability at least `1 - δ` on which
every `ε`-approximate trajectory `a` of mirror descent on the simplex with the negative entropy
and learning rate `√(log d / T)`, started at the uniform point and with positive coordinates, has
regret at most `2 √(T log d)` against every point of the simplex. -/
theorem approxMirrorDescent_regret_le_negEntropy_iid {P : Measure Ω} [IsProbabilityMeasure P]
    (ℓ : ℕ → Ω → α → ℝ) (hℓ_meas : ∀ t, Measurable (ℓ t)) (hℓ_indep : iIndepFun ℓ P)
    (hℓ_ident : ∀ t, IdentDistrib (ℓ t) (ℓ 0) P P) (hℓ : ∀ t ω i, ℓ t ω i ∈ Set.Icc (-1) 1)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {T : ℕ} (hT : 256 * log (Fintype.card α) ≤ T)
    (hε : ε ≤ δ / (6 * (Fintype.card α : ℝ) ^ 3 * (T : ℝ) ^ 4)) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - δ ≤ P.real E ∧ ∀ ω ∈ E, ∀ a : ℕ → α → ℝ,
      a 0 = (fun _ ↦ (Fintype.card α : ℝ)⁻¹) → (∀ t ≤ T, ∀ i, 0 < a t i) →
      (∀ t < T, IsApproxMirrorDescentStep (simplex α) negEntropy √(log (Fintype.card α) / T)
        (∑ i, ℓ t ω i • ContinuousLinearMap.proj i) (a t)
        (∑ i, log (a t i) • ContinuousLinearMap.proj i) ε (a (t + 1))) →
      ∀ u ∈ simplex α, regret (fun t w ↦ ∑ i, ℓ t ω i * w i) a u T ≤
        2 * √(T * log (Fintype.card α)) := by
  rcases le_or_gt (Fintype.card α) 1 with hd1 | hd2
  · -- at most one arm: every regret is `0`
    refine ⟨Set.univ, MeasurableSet.univ, by simp [hδ.le], fun ω _ a ha0 _ ha u hu ↦ ?_⟩
    have : Nonempty α := nonempty_of_mem_simplex hu
    have : Subsingleton α := Fintype.card_le_one_iff_subsingleton.1 hd1
    have h_one (w : α → ℝ) (hw : w ∈ simplex α) (k : α) : w k = 1 := by
      have := (mem_simplex_iff.1 hw).2
      rwa [Fintype.sum_subsingleton _ k] at this
    have hmem (t : ℕ) (ht : t ≤ T) : a t ∈ simplex α := by
      cases t with
      | zero => rw [ha0]; exact uniform_mem_simplex α
      | succ t => exact (ha t (by omega)).mem
    have hcard : (Fintype.card α : ℝ) = 1 := by
      exact_mod_cast le_antisymm hd1 Fintype.card_pos
    rw [regret_def, hcard, log_one, mul_zero, sqrt_zero, mul_zero]
    refine (sum_eq_zero fun t ht ↦ ?_).le
    simp only [h_one _ (hmem t (mem_range.1 ht).le), h_one _ hu, sub_self]
  -- at least two arms
  have hd : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hd2
  have hL : 0 < log (Fintype.card α) := log_pos (by linarith)
  have hT0 : (0 : ℝ) < T := by nlinarith
  have hTne : T ≠ 0 := by rintro rfl; simp at hT0
  obtain ⟨E, hE, hPE, hbal⟩ :=
    exists_measurableSet_sum_Ico_sub_le_of_iid ℓ hℓ_meas hℓ_indep hℓ_ident hℓ hδ hδ1 hTne
  refine ⟨E, hE, hPE, fun ω hω a ha0 hpos ha u hu ↦ ?_⟩
  have : Nonempty α := nonempty_of_mem_simplex hu
  obtain ⟨iStar, -, hbest⟩ :=
    exists_min_image univ (fun i ↦ ∑ t ∈ range T, ℓ t ω i) univ_nonempty
  have hη : 0 < √(log (Fintype.card α) / T) := sqrt_pos.2 (div_pos hL hT0)
  have hη16 : √(log (Fintype.card α) / T) ≤ 1 / 16 := by
    calc √(log (Fintype.card α) / T) ≤ √((1 / 16) ^ 2) :=
          sqrt_le_sqrt (by rw [div_le_iff₀ hT0]; linarith)
      _ = 1 / 16 := sqrt_sq (by norm_num)
  -- Lemma 15, with the threshold of `div_le_exp_neg_mul_min_div`
  refine (approxMirrorDescent_regret_le_negEntropy_of_balanced hη hη16 (fun t ↦ ℓ t ω)
    (fun t _ i ↦ abs_le.2 (hℓ t ω i)) iStar (fun i ↦ hbest i (mem_univ i))
    (fun s t hst htT i ↦ hbal ω hω iStar (fun i ↦ hbest i (mem_univ i)) s t hst htT i)
    (hε.trans (div_le_exp_neg_mul_min_div hd hT hδ hδ1)) a ha0 hpos ha hu).trans (le_of_eq ?_)
  -- `log d / η + η T = 2 √(T log d)`
  set L := log (Fintype.card α)
  have hη2 : √(L / T) ^ 2 = L / T := sq_sqrt (div_pos hL hT0).le
  have hsqrt : √(T * L) = √(L / T) * T := by
    rw [show (T : ℝ) * L = (√(L / T) * T) ^ 2 by rw [mul_pow, hη2]; field_simp]
    exact sqrt_sq (by positivity)
  have h1 : L / √(L / T) = √(L / T) * T := by
    rw [div_eq_iff hη.ne', show √(L / T) * T * √(L / T) = √(L / T) ^ 2 * T by ring, hη2]
    field_simp
  rw [h1, hsqrt]
  ring

end Schlisselberg2026Hidden
