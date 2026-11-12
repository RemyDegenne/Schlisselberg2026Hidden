/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ExponentiatedGradient
public import Schlisselberg2026Hidden.ForLMLExplore.Analysis.Convex.PowerBarrier
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Lemma 34 of [SSKM26]: stuck trajectories

The lower bounds of [SSKM26] build trajectories of approximate mirror descent that stay put: for a
loss that is constant off one coordinate `i₀`, staying at a point `w` whose coordinate `i₀` is small
costs only a small error, so it is an approximate step, while the exact step would move `w` toward
`i₀`.

For the negative entropy on the simplex, the error of staying put is
`η ⟨ℓ, w⟩ + log ∑ a, w a e^{-η ℓ a}`
(`LMLExplore.OnlineLearning.isApproxMirrorDescentStep_negEntropy_self_iff`), which for the loss
`1 - e_{i₀}` and `m = w i₀` is at most `η² min (m, 1 - m)` when `η ≤ 1`.

For a power barrier `r` with exponent `ν` and lower constant `c₁`, the error of staying at `w` on
the open simplex is at most `(e / 2) η² m^ν / c₁` when `η ≤ c₁ m^{1-ν} / (3 ν)`: this is a
one-dimensional bound, `η |y - x| - D_r(y, x) ≤ (e / 2) η² x^ν / c₁` for `x, y ∈ (0, 1)`, which
replaces Lemma 24 of [SSKM26] in the proof. The paper bounds the curvature of `r` at the current
point only, while the exact step moves the stuck coordinate up, where the curvature is smaller;
`r'' ≥ c₁ / (e x^ν)` holds up to `x (1 + 1 / ν)`, and beyond that point the slope of `D_r(·, x)`
exceeds `η`.

The paper's Lemma 34 is false for large `η` (`notes/paper-errata.md`).

## Main statements

* `Schlisselberg2026Hidden.isApproxMirrorDescentStep_negEntropy_self`: [SSKM26, Lemma 34] for the
  negative entropy, corrected.
* `Schlisselberg2026Hidden.mul_abs_sub_sub_le_of_isPowerBarrier`: the one-dimensional bound that
  replaces Lemma 24 of [SSKM26] for power barriers.
* `Schlisselberg2026Hidden.isApproxMirrorDescentStep_self_of_isPowerBarrier`: [SSKM26, Lemma 34]
  for power barriers, corrected.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α]

/-- The loss of a point `w` with `∑ a, w a = 1` for a loss `ℓ` that is constant, equal to `c`, off
a coordinate `i₀`: `⟨ℓ, w⟩ = c + (ℓ i₀ - c) w i₀`. -/
lemma sum_mul_eq_add_mul_of_forall_ne {ℓ w : α → ℝ} (hw : ∑ a, w a = 1) {i₀ : α} {c : ℝ}
    (hℓ : ∀ j ≠ i₀, ℓ j = c) :
    ∑ a, ℓ a * w a = c + (ℓ i₀ - c) * w i₀ := by
  classical
  have h : ∀ a, ℓ a * w a = c * w a + if a = i₀ then (ℓ i₀ - c) * w i₀ else 0 := by
    intro a
    split_ifs with ha
    · subst ha
      ring
    · rw [hℓ a ha]
      ring
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum, hw, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, mul_one]

/-- A sum of a function that is constant, equal to `c`, off a coordinate `i₀`. -/
lemma sum_eq_add_mul_of_forall_ne {f : α → ℝ} {i₀ : α} {c : ℝ} (hf : ∀ j ≠ i₀, f j = c) :
    ∑ a, f a = f i₀ + (Fintype.card α - 1) * c := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
    Finset.sum_congr rfl fun j hj ↦ hf j (Finset.ne_of_mem_erase hj), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, nsmul_eq_mul,
    Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨i₀⟩), Nat.cast_one]

/-- The coordinates of a point of the open simplex in dimension at least `2` lie in `(0, 1)`. -/
lemma mem_Ioo_of_forall_pos_of_sum_eq_one (h2 : 2 ≤ Fintype.card α) {w : α → ℝ}
    (hw : (∀ i, 0 < w i) ∧ ∑ i, w i = 1) (i : α) : w i ∈ Set.Ioo 0 1 := by
  classical
  refine ⟨hw.1 i, ?_⟩
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i
  have h : w i + w j ≤ ∑ k, w k := by
    rw [← Finset.sum_pair hj.symm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun k _ _ ↦ (hw.1 k).le
  linarith [hw.1 j, hw.2]

/-- **Staying put with the negative entropy** [SSKM26, Lemma 34] for the negative entropy,
corrected. Let `w` be a point of the simplex with positive coordinates and `ℓ` the loss that is `0`
at `i₀` and `1` elsewhere. If `0 ≤ η ≤ 1` and `ε ≥ η² min (w i₀, 1 - w i₀)`, then staying at `w` is
an `ε`-approximate step of mirror descent with the negative entropy. -/
lemma isApproxMirrorDescentStep_negEntropy_self {w : α → ℝ} (hw : w ∈ simplex α)
    (hpos : ∀ a, 0 < w a) {i₀ : α} {ℓ : α → ℝ} (hℓ₀ : ℓ i₀ = 0) (hℓ : ∀ j ≠ i₀, ℓ j = 1)
    {η ε : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (hε : η ^ 2 * min (w i₀) (1 - w i₀) ≤ ε) :
    IsApproxMirrorDescentStep (simplex α) negEntropy η (∑ a, ℓ a • ContinuousLinearMap.proj a) w
      (∑ a, log (w a) • ContinuousLinearMap.proj a) ε w := by
  rw [isApproxMirrorDescentStep_negEntropy_self_iff hw hpos]
  have hw1 := (mem_simplex_iff.mp hw).2
  set m := w i₀ with hm_def
  have hm0 : 0 ≤ m := (hpos i₀).le
  have hm1 : m ≤ 1 :=
    hw1 ▸ Finset.single_le_sum (fun a _ ↦ (hpos a).le) (Finset.mem_univ i₀)
  have hsum : ∑ a, ℓ a * w a = 1 - m := by
    rw [sum_mul_eq_add_mul_of_forall_ne hw1 hℓ, hℓ₀]
    ring
  have hZ : ∑ a, w a * exp (-(η * ℓ a)) = exp (-η) + (1 - exp (-η)) * m := by
    have h := sum_mul_eq_add_mul_of_forall_ne (ℓ := fun a ↦ exp (-(η * ℓ a))) hw1
      (i₀ := i₀) (c := exp (-η)) fun j hj ↦ by simp [hℓ j hj]
    simp only [hℓ₀, mul_zero, neg_zero, exp_zero] at h
    rw [Finset.sum_congr rfl fun a _ ↦ mul_comm (w a) _, h, hm_def]
  rw [hsum, hZ]
  have hexp : exp (-η) * exp η = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
  have he1 : exp η - 1 - η ≤ η ^ 2 := by
    have := abs_exp_sub_one_sub_id_le (x := η) (by rw [abs_of_nonneg hη]; exact hη1)
    exact (abs_le.mp this).2
  have he2 : exp (-η) - 1 + η ≤ η ^ 2 := by
    have := abs_exp_sub_one_sub_id_le (x := -η) (by rw [abs_neg, abs_of_nonneg hη]; exact hη1)
    have h := (abs_le.mp this).2
    rw [neg_sq] at h
    linarith
  have hexpη : 1 ≤ exp η := one_le_exp hη
  have hZpos : 0 < exp (-η) + (1 - exp (-η)) * m := by
    have : exp (-η) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    nlinarith [exp_pos (-η)]
  -- the error of staying put is at most `η² (1 - m)`
  have hb2 : η * (1 - m) + log (exp (-η) + (1 - exp (-η)) * m) ≤ η ^ 2 * (1 - m) := by
    have h := log_le_sub_one_of_pos hZpos
    nlinarith
  -- the error of staying put is at most `η² m`
  have hb1 : η * (1 - m) + log (exp (-η) + (1 - exp (-η)) * m) ≤ η ^ 2 * m := by
    have hpos' : 0 < 1 + (exp η - 1) * m := by nlinarith
    have hfac : exp (-η) + (1 - exp (-η)) * m = exp (-η) * (1 + (exp η - 1) * m) := by
      linear_combination (-m) * hexp
    rw [hfac, log_mul (exp_pos _).ne' hpos'.ne', log_exp]
    have h := log_le_sub_one_of_pos hpos'
    nlinarith
  calc η * (1 - m) + log (exp (-η) + (1 - exp (-η)) * m)
      ≤ min (η ^ 2 * m) (η ^ 2 * (1 - m)) := le_min hb1 hb2
    _ = η ^ 2 * min m (1 - m) := (mul_min_of_nonneg _ _ (sq_nonneg η)).symm
    _ ≤ ε := hε

/-- **The one-dimensional step bound for power barriers**, which replaces Lemma 24 of [SSKM26] in
the lower bounds. Let `r` be a power barrier with exponent `ν` and lower constant `c₁`,
`x, y ∈ (0, 1)` and `η ≤ c₁ x^{1-ν} / (3 ν)`. Then
`η |y - x| - D_r(y, x) ≤ (e / 2) η² x^ν / c₁`, where `D_r(y, x) = r y - r x - r' x (y - x)`.
Neither the upper constant `c₂` nor the sign of `η` is used. -/
lemma mul_abs_sub_sub_le_of_isPowerBarrier {ν c₁ c₂ : ℝ} {r : ℝ → ℝ}
    (hr : IsPowerBarrier ν c₁ c₂ r) {x y η : ℝ} (hx : x ∈ Set.Ioo 0 1) (hy : y ∈ Set.Ioo 0 1)
    (hηx : η ≤ c₁ * x ^ (1 - ν) / (3 * ν)) :
    η * |y - x| - (r y - r x - deriv r x * (y - x)) ≤ exp 1 / 2 * η ^ 2 * x ^ ν / c₁ := by
  have hν0 : 0 < ν := one_pos.trans_le hr.one_le
  have hxν : 0 < x ^ ν := rpow_pos_of_pos hx.1 ν
  set κ := c₁ / (exp 1 * x ^ ν) with hκ_def
  have hκ : 0 < κ := div_pos hr.pos (mul_pos (exp_pos 1) hxν)
  set z := x * (1 + 1 / ν) with hz_def
  have hxz : x ≤ z := le_mul_of_one_le_right hx.1.le (by linarith [one_div_pos.mpr hν0])
  -- the curvature is at least `κ` up to `z`
  have hA0 : ∀ s ∈ Set.Ioo (0 : ℝ) 1, s ≤ z → κ ≤ deriv (deriv r) s := by
    intro s hs hsz
    refine le_trans ?_ (hr.le_deriv_deriv s hs)
    have h1 : s ^ ν ≤ z ^ ν := rpow_le_rpow hs.1.le hsz hν0.le
    have h2 : z ^ ν ≤ exp 1 * x ^ ν := by
      rw [hz_def, mul_rpow hx.1.le (by positivity), mul_comm]
      gcongr
      calc (1 + 1 / ν) ^ ν ≤ (exp (1 / ν)) ^ ν :=
            rpow_le_rpow (by positivity) (by linarith [add_one_le_exp (1 / ν)]) hν0.le
        _ = exp 1 := by rw [← exp_mul, one_div_mul_cancel hν0.ne']
    exact div_le_div_of_nonneg_left hr.pos.le (rpow_pos_of_pos hs.1 ν) (h1.trans h2)
  -- the bound for `y ≤ z`
  have hA2 : ∀ y ∈ Set.Ioo (0 : ℝ) 1, y ≤ z →
      η * |y - x| - (r y - r x - deriv r x * (y - x)) ≤ exp 1 / 2 * η ^ 2 * x ^ ν / c₁ := by
    intro y hy hyz
    have hD := hr.mul_sq_le_sub_sub (κ := κ) hy hx fun s hs ↦
      hA0 s (Set.ordConnected_Ioo.uIcc_subset hy hx hs) (hs.2.trans (max_le hyz hxz))
    rw [← sq_abs] at hD
    have key : η * |y - x| - κ * |y - x| ^ 2 / 2 ≤ η ^ 2 / (2 * κ) := by
      have h1 : η ^ 2 / (2 * κ) - (η * |y - x| - κ * |y - x| ^ 2 / 2) =
          (η - κ * |y - x|) ^ 2 / (2 * κ) := by
        field_simp
        ring
      have h2 : 0 ≤ (η - κ * |y - x|) ^ 2 / (2 * κ) := by positivity
      linarith
    have h3 : η ^ 2 / (2 * κ) = exp 1 / 2 * η ^ 2 * x ^ ν / c₁ := by
      rw [hκ_def]
      field_simp
    linarith
  by_cases hyz : y ≤ z
  · exact hA2 y hy hyz
  rw [not_le] at hyz
  have hz : z ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx.1.trans_le hxz, hyz.trans hy.2⟩
  -- beyond `z`, the slope of `D_r(·, x)` exceeds `η`
  have hdz : κ * (z - x) ≤ deriv r z - deriv r x :=
    hr.mul_sub_le_deriv_sub hx hz hxz fun s hs ↦ hA0 s (Set.Icc_subset_Ioo hx.1 hz.2 hs) hs.2
  have hκz : η ≤ κ * (z - x) := by
    have h1 : κ * (z - x) = c₁ * x ^ (1 - ν) / (exp 1 * ν) := by
      rw [hκ_def, hz_def, rpow_sub hx.1, rpow_one]
      field_simp
      ring
    rw [h1]
    refine hηx.trans (div_le_div_of_nonneg_left
      (mul_nonneg hr.pos.le (rpow_nonneg hx.1.le _)) (mul_pos (exp_pos 1) hν0) ?_)
    exact mul_le_mul_of_nonneg_right (Real.exp_one_lt_d9.le.trans (by norm_num)) hν0.le
  have hDyz := hr.sub_sub_nonneg hy hz
  have hAz := hA2 z hz le_rfl
  rw [abs_of_nonneg (by linarith : 0 ≤ y - x)]
  rw [abs_of_nonneg (by linarith : 0 ≤ z - x)] at hAz
  have hprod : 0 ≤ (deriv r z - deriv r x - η) * (y - z) :=
    mul_nonneg (by linarith) (by linarith)
  have hid : η * (y - x) - (r y - r x - deriv r x * (y - x)) =
      (η * (z - x) - (r z - r x - deriv r x * (z - x))) - (r y - r z - deriv r z * (y - z)) -
        (deriv r z - deriv r x - η) * (y - z) := by ring
  rw [hid]
  linarith

/-- **Staying put with a power barrier** [SSKM26, Lemma 34] for power barriers, corrected. Let the
simplex have at least two coordinates, `r` be a power barrier with exponent `ν` and lower constant
`c₁`, `w` a point of the open simplex and `ℓ` a loss constant, equal to `c`, off a coordinate `i₀`,
with `|c - ℓ i₀| ≤ 1` (for instance a loss in `[0, 1]^d` constant off `i₀`). If
`0 ≤ η ≤ c₁ (w i₀)^{1-ν} / (3 ν)` and `ε ≥ 2 η² (w i₀)^ν / c₁`, then staying at `w` is an
`ε`-approximate step of mirror descent on the open simplex with the potential
`w ↦ ∑ i, r (w i)`. The upper constant `c₂` is not used. -/
lemma isApproxMirrorDescentStep_self_of_isPowerBarrier (h2 : 2 ≤ Fintype.card α)
    {ν c₁ c₂ : ℝ} {r : ℝ → ℝ} (hr : IsPowerBarrier ν c₁ c₂ r) {w : α → ℝ}
    (hw : w ∈ {w : α → ℝ | (∀ i, 0 < w i) ∧ ∑ i, w i = 1}) {i₀ : α} {ℓ : α → ℝ} {c : ℝ}
    (hℓ : ∀ j ≠ i₀, ℓ j = c) (hc : |c - ℓ i₀| ≤ 1) {η ε : ℝ} (hη : 0 ≤ η)
    (hηw : η ≤ c₁ * w i₀ ^ (1 - ν) / (3 * ν)) (hε : 2 * η ^ 2 * w i₀ ^ ν / c₁ ≤ ε) :
    IsApproxMirrorDescentStep {w : α → ℝ | (∀ i, 0 < w i) ∧ ∑ i, w i = 1}
      (fun w ↦ ∑ i, r (w i)) η (∑ i, ℓ i • ContinuousLinearMap.proj i) w
      (∑ i, deriv r (w i) • ContinuousLinearMap.proj i) ε w := by
  refine ⟨hw, fun b hb ↦ ?_⟩
  have hwI := mem_Ioo_of_forall_pos_of_sum_eq_one h2 hw
  have hbI := mem_Ioo_of_forall_pos_of_sum_eq_one h2 hb
  rw [bregDiv_sum_apply, bregDiv_sum_apply]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, sub_self,
    mul_zero, Finset.sum_const_zero, add_zero]
  rw [sum_mul_eq_add_mul_of_forall_ne hw.2 hℓ, sum_mul_eq_add_mul_of_forall_ne hb.2 hℓ]
  -- the loss part
  have hloss : η * ((ℓ i₀ - c) * (w i₀ - b i₀)) ≤ η * |b i₀ - w i₀| := by
    refine mul_le_mul_of_nonneg_left ?_ hη
    calc (ℓ i₀ - c) * (w i₀ - b i₀) ≤ |(ℓ i₀ - c) * (w i₀ - b i₀)| := le_abs_self _
      _ = |c - ℓ i₀| * |b i₀ - w i₀| := by rw [abs_mul, abs_sub_comm, abs_sub_comm (w i₀)]
      _ ≤ 1 * |b i₀ - w i₀| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
      _ = |b i₀ - w i₀| := one_mul _
  -- the divergence part
  have hdiv : r (b i₀) - r (w i₀) - deriv r (w i₀) * (b i₀ - w i₀) ≤
      ∑ i, (r (b i) - r (w i) - deriv r (w i) * (b i - w i)) :=
    Finset.single_le_sum (f := fun i ↦ r (b i) - r (w i) - deriv r (w i) * (b i - w i))
      (fun i _ ↦ hr.sub_sub_nonneg (hbI i) (hwI i)) (Finset.mem_univ i₀)
  have hstep := mul_abs_sub_sub_le_of_isPowerBarrier hr (hwI i₀) (hbI i₀) hηw
  have he : exp 1 / 2 * η ^ 2 * w i₀ ^ ν / c₁ ≤ 2 * η ^ 2 * w i₀ ^ ν / c₁ := by
    have hpos : 0 ≤ η ^ 2 * w i₀ ^ ν / c₁ :=
      div_nonneg (mul_nonneg (sq_nonneg η) (rpow_nonneg (hw.1 i₀).le ν)) hr.pos.le
    have h1 : exp 1 / 2 ≤ 2 := by linarith [exp_one_lt_d9]
    calc exp 1 / 2 * η ^ 2 * w i₀ ^ ν / c₁ = exp 1 / 2 * (η ^ 2 * w i₀ ^ ν / c₁) := by ring
      _ ≤ 2 * (η ^ 2 * w i₀ ^ ν / c₁) := mul_le_mul_of_nonneg_right h1 hpos
      _ = 2 * η ^ 2 * w i₀ ^ ν / c₁ := by ring
  have hexpand : η * (c + (ℓ i₀ - c) * w i₀) =
      η * (c + (ℓ i₀ - c) * b i₀) + η * ((ℓ i₀ - c) * (w i₀ - b i₀)) := by ring
  rw [hexpand]
  linarith

end Schlisselberg2026Hidden
