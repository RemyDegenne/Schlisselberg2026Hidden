/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Bregman.Basic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Real.Sqrt

/-!
# The approximate first-order condition of an `ε`-minimizer

At a minimizer `x` of a differentiable function `f` on a convex set `K`, the derivative is
nonnegative towards every point of `K`: `f' (w - x) ≥ 0` for `w ∈ K`. At an `ε`-minimizer, a point
`x ∈ K` with `f x ≤ f b + ε` for all `b ∈ K`, this fails, but only by a controlled amount when `f`
has a quadratic upper bound `f z ≤ f x + f' (z - x) + β / 2 * ‖z - x‖ ^ 2` around `x`, as a
`β`-smooth function has (`Convex.bregDiv_le_mul_norm_sub_sq`):
`f' (w - x) ≥ -max (‖w - x‖ √(2 β ε)) (2 ε)` [SSKM26, Lemma 22]. Comparing `x` with the points
`x + γ (w - x)`, `γ ∈ (0, 1]`, gives `f' (w - x) ≥ -ε / γ - γ β ‖w - x‖² / 2`, and the bound is
the best choice of `γ`.

The statements only use the two inequalities on the segment `[x, w]`, so they need neither a
convex set nor a derivative: `f'` is any linear map for which the quadratic upper bound holds,
written with the Bregman divergence `D_f(z, x) = f z - f x - f' (z - x)`.

## Main statements

* `LMLExplore.neg_max_le_apply_sub_of_le_add`: [SSKM26, Lemma 22]. If `f x ≤ f z + ε` and
  `D_f(z, x) ≤ β / 2 * ‖z - x‖ ^ 2` for `z` on the segment `[x, w]`, then
  `-max (‖w - x‖ √(2 β ε)) (2 ε) ≤ f' (w - x)`.
* `LMLExplore.neg_mul_sqrt_le_apply_sub_of_le_add`: [SSKM26, Lemma 22], second claim. If moreover
  `‖w - x‖ ≤ D` and `ε ≤ β D² / 2`, then `-(D √(2 β ε)) ≤ f' (w - x)`.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

public section

namespace LMLExplore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ}
  {x w : E} {β ε : ℝ}

/-- **Approximate first-order condition** [SSKM26, Lemma 22]. Let `x` be an `ε`-minimizer of `f`
on the segment `[x, w]` (`f x ≤ f z + ε` there), and let `f` satisfy the quadratic upper bound
`D_f(z, x) = f z - f x - f' (z - x) ≤ β / 2 * ‖z - x‖ ^ 2` on the segment. Then
`-max (‖w - x‖ √(2 β ε)) (2 ε) ≤ f' (w - x)`.

The paper assumes `x` to be an `ε`-minimizer on a convex set `K` containing `w`, `f'` to be the
gradient of `f` at `x` and `β > 0`; the proof uses none of these beyond the segment. Its proof
writes the bound of the second case with the wrong sign (erratum E15). -/
lemma neg_max_le_apply_sub_of_le_add (hmin : ∀ z ∈ segment ℝ x w, f x ≤ f z + ε)
    (hquad : ∀ z ∈ segment ℝ x w, bregDiv f z x f' ≤ β / 2 * ‖z - x‖ ^ 2) :
    -max (‖w - x‖ * √(2 * β * ε)) (2 * ε) ≤ f' (w - x) := by
  set v := w - x with hv
  set L := f' v with hL
  have hε : 0 ≤ ε := by simpa using hmin x (left_mem_segment ℝ x w)
  -- comparing `x` with `x + γ v` for `γ ∈ (0, 1]`: `-ε ≤ γ L + γ² β ‖v‖² / 2`
  have hγ (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
      -ε ≤ γ * L + γ ^ 2 * (β / 2 * ‖v‖ ^ 2) := by
    have hz : x + γ • v ∈ segment ℝ x w := by
      rw [segment_eq_image']
      exact ⟨γ, ⟨hγ0.le, hγ1⟩, rfl⟩
    have h1 := hmin _ hz
    have h2 := hquad _ hz
    simp only [bregDiv, add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs,
      abs_of_pos hγ0, mul_pow] at h2
    linarith
  rcases le_or_gt (β * ‖v‖ ^ 2) (2 * ε) with h | h
  · -- `γ = 1` gives `L ≥ -ε - β ‖v‖² / 2 ≥ -2 ε`
    have h1 := hγ 1 one_pos le_rfl
    refine (neg_le_neg (le_max_right _ _)).trans ?_
    linarith
  have hβ : 0 < β := by
    by_contra! hβ
    nlinarith [sq_nonneg ‖v‖]
  have hv0 : 0 < ‖v‖ := by
    by_contra! hv0
    have : ‖v‖ = 0 := le_antisymm hv0 (norm_nonneg v)
    rw [this] at h
    linarith
  refine (neg_le_neg (le_max_left _ _)).trans ?_
  rcases hε.eq_or_lt with rfl | hε0
  · -- `ε = 0`: `L ≥ -γ β ‖v‖² / 2` for every `γ ∈ (0, 1]`, so `L ≥ 0`
    simp only [mul_zero, Real.sqrt_zero, neg_zero]
    refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
    set c := β / 2 * ‖v‖ ^ 2 with hc
    have hc0 : 0 < c := by positivity
    set γ := min 1 (δ / c) with hγ_def
    have hγ0 : 0 < γ := lt_min one_pos (div_pos hδ hc0)
    have hγc : γ * c ≤ δ := by
      calc γ * c ≤ δ / c * c := mul_le_mul_of_nonneg_right (min_le_right _ _) hc0.le
      _ = δ := div_mul_cancel₀ δ hc0.ne'
    have h1 := hγ γ hγ0 (min_le_left _ _)
    have h2 : γ * 0 ≤ γ * (L + γ * c) := by linarith
    have h3 := le_of_mul_le_mul_left h2 hγ0
    linarith
  · -- `γ = √(2 ε / β) / ‖v‖ ∈ (0, 1)` gives `L ≥ -‖v‖ √(2 β ε)`
    set r := √(2 * ε / β) with hr
    have hr0 : 0 < r := Real.sqrt_pos.mpr (by positivity)
    have hr2 : r ^ 2 = 2 * ε / β := Real.sq_sqrt (by positivity)
    have hsqrt : √(2 * β * ε) = β * r := by
      rw [hr, show 2 * β * ε = β ^ 2 * (2 * ε / β) by field_simp, Real.sqrt_mul (sq_nonneg β),
        Real.sqrt_sq hβ.le]
    have hrv : r ≤ ‖v‖ := by
      rw [hr, Real.sqrt_le_left (by positivity)]
      rw [div_le_iff₀ hβ]
      linarith
    have h1 := hγ (r / ‖v‖) (div_pos hr0 hv0) ((div_le_one hv0).mpr hrv)
    have h2 : (r / ‖v‖) ^ 2 * (β / 2 * ‖v‖ ^ 2) = ε := by
      rw [div_pow, hr2]
      field_simp
    rw [h2] at h1
    -- `r L ≥ -2 ε ‖v‖ = -β r² ‖v‖`
    have h3 : r * (-(β * r * ‖v‖)) ≤ r * L := by
      have h4 : r / ‖v‖ * L * ‖v‖ = r * L := by field_simp
      have h5 : -(2 * ε) * ‖v‖ ≤ r / ‖v‖ * L * ‖v‖ :=
        mul_le_mul_of_nonneg_right (by linarith) hv0.le
      have h6 : β * r ^ 2 = 2 * ε := by rw [hr2]; field_simp
      nlinarith
    rw [hsqrt]
    have := le_of_mul_le_mul_left h3 hr0
    linarith

/-- **Approximate first-order condition with a diameter** [SSKM26, Lemma 22]. Under the assumptions
of `neg_max_le_apply_sub_of_le_add`, if `‖w - x‖ ≤ D` and `ε ≤ β D² / 2`, then
`-(D √(2 β ε)) ≤ f' (w - x)`. -/
lemma neg_mul_sqrt_le_apply_sub_of_le_add {D : ℝ} (hwD : ‖w - x‖ ≤ D) (hεD : ε ≤ β * D ^ 2 / 2)
    (hmin : ∀ z ∈ segment ℝ x w, f x ≤ f z + ε)
    (hquad : ∀ z ∈ segment ℝ x w, bregDiv f z x f' ≤ β / 2 * ‖z - x‖ ^ 2) :
    -(D * √(2 * β * ε)) ≤ f' (w - x) := by
  refine (neg_le_neg ?_).trans (neg_max_le_apply_sub_of_le_add hmin hquad)
  have hε : 0 ≤ ε := by simpa using hmin x (left_mem_segment ℝ x w)
  have hD : 0 ≤ D := (norm_nonneg _).trans hwD
  refine max_le (mul_le_mul_of_nonneg_right hwD (Real.sqrt_nonneg _)) ?_
  -- `(2 ε)² ≤ D² (2 β ε)` since `2 ε ≤ β D²`
  rw [← Real.sqrt_sq hD, ← Real.sqrt_mul (sq_nonneg D)]
  refine Real.le_sqrt_of_sq_le ?_
  nlinarith

end LMLExplore
