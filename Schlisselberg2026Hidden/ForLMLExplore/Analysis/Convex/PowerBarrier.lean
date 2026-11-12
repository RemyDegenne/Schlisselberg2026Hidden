/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import LMLExplore.Analysis.Convex.Bregman.Taylor

/-!
# Power barriers

A function `r : ℝ → ℝ` is a **power barrier** with exponent `ν ≥ 1` and constants `0 < c₁` and
`c₂` if it is twice differentiable on `(0, 1)` with `c₁ / x ^ ν ≤ r'' x ≤ c₂ / x ^ ν` there. The
coordinate-separable regularizer `w ↦ ∑ i, r (w i)` on the probability simplex is then a barrier
for the positive orthant: its curvature blows up like `x ^ (-ν)` at the boundary. This is the
class of "coordinate separable barrier regularizers with parameter `ν`" of [SSKM26, Definition 1],
which contains the negative entropy `x log x` (`ν = 1`, `c₁ = c₂ = 1`), the Tsallis entropies
`(x - x ^ q) / (1 - q)` for `q ∈ (0, 1)` (`ν = 2 - q`, `c₁ = c₂ = q`) and the log barrier `-log x`
(`ν = 2`, `c₁ = c₂ = 1`).

[SSKM26] asks the bounds on `(0, 1]` for a function on `[0, 1]`. The points of the simplex of
dimension at least `2` with positive coordinates have coordinates in `(0, 1)`, and so do the
segments between them, so the open interval is what the analysis of mirror descent uses.

The scalar Bregman divergence of `r` is written `r x - r y - deriv r y * (x - y)`. Taylor's
formula with Lagrange remainder of order two (`Convex.exists_mem_segment_sub_sub_mul_eq`, from
LMLExplore's `Convex.exists_mem_segment_bregDiv_eq`) gives it the value `r'' z * (x - y) ^ 2 / 2` at
a point `z` between `x` and `y`, from which all the bounds below follow.

## Main definitions

* `LMLExplore.IsPowerBarrier ν c₁ c₂ r`: `r` is twice differentiable on `(0, 1)` with
  `c₁ / x ^ ν ≤ r'' x ≤ c₂ / x ^ ν` there, for `ν ≥ 1` and `c₁ > 0`.

## Main statements

* `LMLExplore.bregDiv_sum_apply`: the Bregman divergence of a coordinate-separable function
  `w ↦ ∑ a, r (w a)` is the sum of the scalar divergences of its coordinates.
* `LMLExplore.hasFDerivAt_sum_apply`, `LMLExplore.IsPowerBarrier.hasFDerivAt_sum`: the derivative
  of a coordinate-separable function.
* `Convex.exists_mem_segment_sub_sub_mul_eq`: Taylor's formula of order two, for a real function
  with a derivative and a second derivative within a convex set.
* `LMLExplore.isPowerBarrier_mul_log`, `LMLExplore.isPowerBarrier_tsallis`,
  `LMLExplore.isPowerBarrier_neg_log`: the negative entropy, the Tsallis entropies and the log
  barrier are power barriers.
* `LMLExplore.IsPowerBarrier.congr`: being a power barrier only depends on the values on `(0, 1)`.
* `LMLExplore.IsPowerBarrier.strictMonoOn_deriv`: the derivative of a power barrier is strictly
  monotone on `(0, 1)`.
* `LMLExplore.IsPowerBarrier.sub_sub_le_mul_sq`: the scalar Bregman divergence is at most
  `M (x - y) ^ 2 / 2` when `r'' ≤ M` between `x` and `y` [SSKM26, Lemma 21].
* `LMLExplore.IsPowerBarrier.sub_sub_nonneg`, `LMLExplore.IsPowerBarrier.mul_sq_le_sub_sub`,
  `LMLExplore.IsPowerBarrier.mul_sq_div_max_le_sub_sub`: the scalar Bregman divergence is
  nonnegative, and has quadratic lower bounds given by lower bounds on `r''`.
* `LMLExplore.IsPowerBarrier.mul_rpow_sub_rpow_le_deriv_sub`: the increments of `r'` for `ν > 1`
  [SSKM26, Lemma 41], with the factor `1 / (ν - 1)` that [SSKM26] omits.
* `LMLExplore.IsPowerBarrier.sub_sub_nonneg_of_continuousWithinAt`,
  `LMLExplore.IsPowerBarrier.sub_sub_nonneg_of_continuousWithinAt_Iic`,
  `LMLExplore.IsPowerBarrier.sub_sub_nonneg_of_mem_Icc`: the scalar Bregman divergence from a
  point of `(0, 1)` to `0` (to `1`) is nonnegative when `r` is right-continuous at `0`
  (left-continuous at `1`). The definition does not constrain `r 0` and `r 1`.
* `LMLExplore.IsPowerBarrier.mul_sq_sum_abs_sub_le_bregDiv`: strong convexity for the `ℓ¹` norm:
  on the points of the simplex with coordinates in `(0, 1)`, the Bregman divergence of
  `w ↦ ∑ a, r (w a)` is at least `c₁ / 4 * ‖y - x‖₁ ^ 2`, so the regularizer is
  `c₁ / 2`-strongly convex there.
* `LMLExplore.IsPowerBarrier.mul_sub_le_deriv_sub`,
  `LMLExplore.IsPowerBarrier.mul_log_div_le_deriv_sub`: the increments of `r'` from a lower bound
  on `r''`, and for `ν = 1`.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open Set Real

/-- **Taylor's formula of order two** with Lagrange remainder, for a real function `f` with a
derivative `f'` and a second derivative `f''` within a convex set `s`: for `x, y ∈ s`, there is a
point `z` between `x` and `y` with `f x - f y - f' y (x - y) = f'' z (x - y) ^ 2 / 2`. No continuity
of `f''` is needed. -/
lemma Convex.exists_mem_segment_sub_sub_mul_eq {f f' f'' : ℝ → ℝ} {s : Set ℝ} (hs : Convex ℝ s)
    {x y : ℝ} (hf : ∀ z ∈ s, HasDerivWithinAt f (f' z) s z)
    (hf' : ∀ z ∈ s, HasDerivWithinAt f' (f'' z) s z) (hx : x ∈ s) (hy : y ∈ s) :
    ∃ z ∈ segment ℝ x y, f x - f y - f' y * (x - y) = f'' z * (x - y) ^ 2 / 2 := by
  set L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)
  have hL : ∀ d k : ℝ, L d k = k * d := fun d k ↦ by simp [L]
  have h1 : ∀ z ∈ s, HasFDerivWithinAt f (L (f' z)) s z := fun z hz ↦ (hf z hz).hasFDerivWithinAt
  have h2 : ∀ z ∈ s, HasFDerivWithinAt (fun z ↦ L (f' z))
      (L.comp (ContinuousLinearMap.toSpanSingleton ℝ (f'' z))) s z := fun z hz ↦
    L.hasFDerivAt.comp_hasFDerivWithinAt z (hf' z hz).hasFDerivWithinAt
  obtain ⟨z, hz, h⟩ := hs.exists_mem_segment_bregDiv_eq h1 h2 hx hy
  refine ⟨z, hz, ?_⟩
  simp only [bregDiv, hL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at h
  rw [mul_comm (f' y), h]
  ring

namespace LMLExplore

/-- The Bregman divergence of a coordinate-separable function `w ↦ ∑ a, r (w a)` on `α → ℝ`, with
the linear map `h ↦ ∑ a, r' (y a) * h a`, is the sum over the coordinates of the scalar
divergences `r (x a) - r (y a) - r' (y a) * (x a - y a)`. -/
lemma bregDiv_sum_apply {α : Type*} [Fintype α] (r r' : ℝ → ℝ) (x y : α → ℝ) :
    bregDiv (fun w : α → ℝ ↦ ∑ a, r (w a)) x y
        (∑ a, r' (y a) • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ) =
      ∑ a, (r (x a) - r (y a) - r' (y a) * (x a - y a)) := by
  simp only [bregDiv, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, Pi.sub_apply,
    smul_eq_mul, Finset.sum_sub_distrib]

/-- The derivative of a coordinate-separable function `w ↦ ∑ a, r (w a)` on `α → ℝ` at a point `w`
at whose coordinates `r` is differentiable is `h ↦ ∑ a, r' (w a) * h a`. -/
lemma hasFDerivAt_sum_apply {α : Type*} [Fintype α] {r : ℝ → ℝ} {w : α → ℝ}
    (h : ∀ a, DifferentiableAt ℝ r (w a)) :
    HasFDerivAt (fun w : α → ℝ ↦ ∑ a, r (w a))
      (∑ a, deriv r (w a) • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ) w :=
  HasFDerivAt.fun_sum fun a _ ↦ (h a).hasDerivAt.comp_hasFDerivAt w (hasFDerivAt_apply a w)

/-- `r` is a **power barrier** with exponent `ν` and constants `c₁`, `c₂` [SSKM26, Definition 1]:
`ν ≥ 1`, `c₁ > 0`, and `r` is twice differentiable on `(0, 1)` with
`c₁ / x ^ ν ≤ r'' x ≤ c₂ / x ^ ν` for `x ∈ (0, 1)`. -/
structure IsPowerBarrier (ν c₁ c₂ : ℝ) (r : ℝ → ℝ) : Prop where
  /-- The exponent is at least `1`. -/
  one_le : 1 ≤ ν
  /-- The lower constant is positive. -/
  pos : 0 < c₁
  /-- `r` is differentiable on `(0, 1)`. -/
  differentiableOn : DifferentiableOn ℝ r (Ioo 0 1)
  /-- The derivative of `r` is differentiable on `(0, 1)`. -/
  differentiableOn_deriv : DifferentiableOn ℝ (deriv r) (Ioo 0 1)
  /-- The lower bound on the second derivative. -/
  le_deriv_deriv : ∀ x ∈ Ioo 0 1, c₁ / x ^ ν ≤ deriv (deriv r) x
  /-- The upper bound on the second derivative. -/
  deriv_deriv_le : ∀ x ∈ Ioo 0 1, deriv (deriv r) x ≤ c₂ / x ^ ν

namespace IsPowerBarrier

variable {ν c₁ c₂ : ℝ} {r : ℝ → ℝ} {x y κ M : ℝ}

/-- A power barrier has its derivative at every point of `(0, 1)`. -/
lemma hasDerivAt (hr : IsPowerBarrier ν c₁ c₂ r) (hx : x ∈ Ioo 0 1) :
    HasDerivAt r (deriv r x) x :=
  (hr.differentiableOn.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt

/-- The derivative of a power barrier has its derivative at every point of `(0, 1)`. -/
lemma hasDerivAt_deriv (hr : IsPowerBarrier ν c₁ c₂ r) (hx : x ∈ Ioo 0 1) :
    HasDerivAt (deriv r) (deriv (deriv r) x) x :=
  (hr.differentiableOn_deriv.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt

/-- The derivative of a power barrier is continuous on `(0, 1)`. -/
lemma continuousOn_deriv (hr : IsPowerBarrier ν c₁ c₂ r) : ContinuousOn (deriv r) (Ioo 0 1) :=
  hr.differentiableOn_deriv.continuousOn

/-- Being a power barrier only depends on the values on `(0, 1)`: a function that agrees with a
power barrier there is a power barrier, whatever its values at `0` and `1`. -/
lemma congr (hr : IsPowerBarrier ν c₁ c₂ r) {r' : ℝ → ℝ} (h : EqOn r' r (Ioo 0 1)) :
    IsPowerBarrier ν c₁ c₂ r' := by
  have h1 : EqOn (deriv r') (deriv r) (Ioo 0 1) := h.deriv isOpen_Ioo
  have h2 : EqOn (deriv (deriv r')) (deriv (deriv r)) (Ioo 0 1) := h1.deriv isOpen_Ioo
  exact ⟨hr.one_le, hr.pos, hr.differentiableOn.congr h, hr.differentiableOn_deriv.congr h1,
    fun x hx ↦ (h2 hx).symm ▸ hr.le_deriv_deriv x hx,
    fun x hx ↦ (h2 hx).symm ▸ hr.deriv_deriv_le x hx⟩

/-- The second derivative of a power barrier is positive on `(0, 1)`. -/
lemma deriv_deriv_pos (hr : IsPowerBarrier ν c₁ c₂ r) (hx : x ∈ Ioo 0 1) :
    0 < deriv (deriv r) x :=
  (div_pos hr.pos (rpow_pos_of_pos hx.1 _)).trans_le (hr.le_deriv_deriv x hx)

/-- The derivative of a power barrier is strictly monotone on `(0, 1)`. -/
lemma strictMonoOn_deriv (hr : IsPowerBarrier ν c₁ c₂ r) : StrictMonoOn (deriv r) (Ioo 0 1) :=
  strictMonoOn_of_deriv_pos (convex_Ioo 0 1) hr.continuousOn_deriv
    (by rw [interior_Ioo]; exact fun x hx ↦ hr.deriv_deriv_pos hx)

/-- **Taylor's formula for a power barrier**: for `x, y ∈ (0, 1)`, the scalar Bregman divergence
`r x - r y - r' y (x - y)` is `r'' z (x - y) ^ 2 / 2` for a point `z` between `x` and `y`. -/
lemma exists_mem_uIcc_sub_sub_eq (hr : IsPowerBarrier ν c₁ c₂ r) (hx : x ∈ Ioo 0 1)
    (hy : y ∈ Ioo 0 1) :
    ∃ z ∈ uIcc x y, r x - r y - deriv r y * (x - y) = deriv (deriv r) z * (x - y) ^ 2 / 2 := by
  rw [← segment_eq_uIcc]
  exact (convex_Ioo 0 1).exists_mem_segment_sub_sub_mul_eq
    (fun z hz ↦ (hr.hasDerivAt hz).hasDerivWithinAt)
    (fun z hz ↦ (hr.hasDerivAt_deriv hz).hasDerivWithinAt) hx hy

/-- The scalar Bregman divergence of a power barrier is bounded below by `κ (x - y) ^ 2 / 2` when
`κ` bounds `r''` below between `x` and `y`. -/
lemma mul_sq_le_sub_sub (hr : IsPowerBarrier ν c₁ c₂ r) (hx : x ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1)
    (hκ : ∀ z ∈ uIcc x y, κ ≤ deriv (deriv r) z) :
    κ * (x - y) ^ 2 / 2 ≤ r x - r y - deriv r y * (x - y) := by
  obtain ⟨z, hz, h⟩ := hr.exists_mem_uIcc_sub_sub_eq hx hy
  rw [h]
  gcongr
  exact hκ z hz

/-- **Effective smoothness** [SSKM26, Lemma 21], in one dimension: the scalar Bregman divergence of
a power barrier is bounded above by `M (x - y) ^ 2 / 2` when `M` bounds `r''` above between `x` and
`y`. -/
lemma sub_sub_le_mul_sq (hr : IsPowerBarrier ν c₁ c₂ r) (hx : x ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1)
    (hM : ∀ z ∈ uIcc x y, deriv (deriv r) z ≤ M) :
    r x - r y - deriv r y * (x - y) ≤ M * (x - y) ^ 2 / 2 := by
  obtain ⟨z, hz, h⟩ := hr.exists_mem_uIcc_sub_sub_eq hx hy
  rw [h]
  gcongr
  exact hM z hz

/-- The scalar Bregman divergence of a power barrier is nonnegative on `(0, 1)`. -/
lemma sub_sub_nonneg (hr : IsPowerBarrier ν c₁ c₂ r) (hx : x ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1) :
    0 ≤ r x - r y - deriv r y * (x - y) := by
  have h := hr.mul_sq_le_sub_sub (κ := 0) hx hy fun z hz ↦
    (hr.deriv_deriv_pos ((ordConnected_Ioo.uIcc_subset hx hy) hz)).le
  simpa using h

/-- The scalar Bregman divergence of a power barrier is at least `c₁ (x - y) ^ 2 / (2 max x y)` on
`(0, 1)`. -/
lemma mul_sq_div_max_le_sub_sub (hr : IsPowerBarrier ν c₁ c₂ r) (hx : x ∈ Ioo 0 1)
    (hy : y ∈ Ioo 0 1) :
    c₁ * (x - y) ^ 2 / (2 * max x y) ≤ r x - r y - deriv r y * (x - y) := by
  have hmax : 0 < max x y := lt_max_of_lt_left hx.1
  have h := hr.mul_sq_le_sub_sub (κ := c₁ / max x y) hx hy fun z hz ↦ by
    have hz' : z ∈ Ioo 0 1 := ordConnected_Ioo.uIcc_subset hx hy hz
    refine le_trans ?_ (hr.le_deriv_deriv z hz')
    have hzmax : z ≤ max x y := hz.2
    have h1 : z ^ ν ≤ z ^ (1 : ℝ) := rpow_le_rpow_of_exponent_ge hz'.1 hz'.2.le hr.one_le
    rw [rpow_one] at h1
    exact div_le_div_of_nonneg_left hr.pos.le (rpow_pos_of_pos hz'.1 _) (h1.trans hzmax)
  calc c₁ * (x - y) ^ 2 / (2 * max x y) = c₁ / max x y * (x - y) ^ 2 / 2 := by
        field_simp
    _ ≤ _ := h

/-- The upper constant of a power barrier is at least its lower constant. -/
lemma le_upper (hr : IsPowerBarrier ν c₁ c₂ r) : c₁ ≤ c₂ := by
  have h : (1 / 2 : ℝ) ∈ Ioo 0 1 := by norm_num
  have h1 := (hr.le_deriv_deriv _ h).trans (hr.deriv_deriv_le _ h)
  exact (div_le_div_iff_of_pos_right (rpow_pos_of_pos (by norm_num) ν)).mp h1

/-- The upper constant of a power barrier is positive. -/
lemma upper_pos (hr : IsPowerBarrier ν c₁ c₂ r) : 0 < c₂ :=
  hr.pos.trans_le hr.le_upper

/-- The second derivative of a power barrier is at most `c₂ / κ ^ ν` at the points of `(0, 1)`
above `κ > 0`. -/
lemma deriv_deriv_le_div_rpow (hr : IsPowerBarrier ν c₁ c₂ r) (hx : x ∈ Ioo 0 1) (hκ : 0 < κ)
    (hκx : κ ≤ x) : deriv (deriv r) x ≤ c₂ / κ ^ ν :=
  (hr.deriv_deriv_le x hx).trans <| div_le_div_of_nonneg_left hr.upper_pos.le
    (rpow_pos_of_pos hκ _) (rpow_le_rpow hκ.le hκx (zero_le_one.trans hr.one_le))

/-- A power barrier is differentiable at every point of `(0, 1)`, so the coordinate-separable
function `w ↦ ∑ a, r (w a)` has the derivative `h ↦ ∑ a, r' (w a) * h a` at every point with
coordinates in `(0, 1)`. -/
lemma hasFDerivAt_sum {α : Type*} [Fintype α] (hr : IsPowerBarrier ν c₁ c₂ r) {w : α → ℝ}
    (hw : ∀ a, w a ∈ Ioo 0 1) :
    HasFDerivAt (fun w : α → ℝ ↦ ∑ a, r (w a))
      (∑ a, deriv r (w a) • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ) w :=
  hasFDerivAt_sum_apply fun a ↦ (hr.hasDerivAt (hw a)).differentiableAt

/-- If a power barrier is right-continuous at `0`, its scalar Bregman divergence
`r x - r y - r' y (x - y)` is nonnegative for `x ∈ [0, 1)` and `y ∈ (0, 1)`: the value `r 0` is
the limit of the values on `(0, 1)`, which lie above the tangent at `y`. -/
lemma sub_sub_nonneg_of_continuousWithinAt (hr : IsPowerBarrier ν c₁ c₂ r)
    (hc : ContinuousWithinAt r (Ici 0) 0) (hx : x ∈ Ico 0 1) (hy : y ∈ Ioo 0 1) :
    0 ≤ r x - r y - deriv r y * (x - y) := by
  rcases hx.1.eq_or_lt with rfl | hx0
  · have h1 : Filter.Tendsto r (nhdsWithin 0 (Ioi 0)) (nhds (r 0)) :=
      (hc.mono Ioi_subset_Ici_self).tendsto
    have h2 : Filter.Tendsto (fun s ↦ r s - r y - deriv r y * (s - y)) (nhdsWithin 0 (Ioi 0))
        (nhds (r 0 - r y - deriv r y * (0 - y))) :=
      (h1.sub tendsto_const_nhds).sub (tendsto_const_nhds.mul
        ((tendsto_nhdsWithin_of_tendsto_nhds Filter.tendsto_id).sub tendsto_const_nhds))
    refine ge_of_tendsto h2 ?_
    filter_upwards [Ioo_mem_nhdsGT hy.1] with s hs
    exact hr.sub_sub_nonneg ⟨hs.1, hs.2.trans hy.2⟩ hy
  · exact hr.sub_sub_nonneg ⟨hx0, hx.2⟩ hy

/-- If a power barrier is left-continuous at `1`, its scalar Bregman divergence
`r x - r y - r' y (x - y)` is nonnegative for `x ∈ (0, 1]` and `y ∈ (0, 1)`. -/
lemma sub_sub_nonneg_of_continuousWithinAt_Iic (hr : IsPowerBarrier ν c₁ c₂ r)
    (hc : ContinuousWithinAt r (Iic 1) 1) (hx : x ∈ Ioc 0 1) (hy : y ∈ Ioo 0 1) :
    0 ≤ r x - r y - deriv r y * (x - y) := by
  rcases hx.2.eq_or_lt with rfl | hx1
  · have h1 : Filter.Tendsto r (nhdsWithin 1 (Iio 1)) (nhds (r 1)) :=
      (hc.mono Iio_subset_Iic_self).tendsto
    have h2 : Filter.Tendsto (fun s ↦ r s - r y - deriv r y * (s - y)) (nhdsWithin 1 (Iio 1))
        (nhds (r 1 - r y - deriv r y * (1 - y))) :=
      (h1.sub tendsto_const_nhds).sub (tendsto_const_nhds.mul
        ((tendsto_nhdsWithin_of_tendsto_nhds Filter.tendsto_id).sub tendsto_const_nhds))
    refine ge_of_tendsto h2 ?_
    filter_upwards [Ioo_mem_nhdsLT hy.2] with s hs
    exact hr.sub_sub_nonneg ⟨hy.1.trans hs.1, hs.2⟩ hy
  · exact hr.sub_sub_nonneg ⟨hx.1, hx1⟩ hy

/-- If a power barrier is right-continuous at `0` and left-continuous at `1`, its scalar Bregman
divergence `r x - r y - r' y (x - y)` is nonnegative for `x ∈ [0, 1]` and `y ∈ (0, 1)`. -/
lemma sub_sub_nonneg_of_mem_Icc (hr : IsPowerBarrier ν c₁ c₂ r)
    (hc₀ : ContinuousWithinAt r (Ici 0) 0) (hc₁ : ContinuousWithinAt r (Iic 1) 1)
    (hx : x ∈ Icc 0 1) (hy : y ∈ Ioo 0 1) : 0 ≤ r x - r y - deriv r y * (x - y) := by
  rcases hx.2.eq_or_lt with h | h
  · exact hr.sub_sub_nonneg_of_continuousWithinAt_Iic hc₁ ⟨h ▸ zero_lt_one, hx.2⟩ hy
  · exact hr.sub_sub_nonneg_of_continuousWithinAt hc₀ ⟨hx.1, h⟩ hy

/-- **Strong convexity of a power barrier for the `ℓ¹` norm.** On the points of the simplex with
coordinates in `(0, 1)`, the Bregman divergence of `w ↦ ∑ a, r (w a)` is at least
`c₁ / 4 * (∑ a, |y a - x a|) ^ 2`: the regularizer is `c₁ / 2`-strongly convex there. The proof
bounds each scalar divergence below by `c₁ (y a - x a) ^ 2 / (2 max (y a) (x a))` and applies the
Cauchy–Schwarz inequality, with `∑ a, max (y a) (x a) ≤ 2`. -/
lemma mul_sq_sum_abs_sub_le_bregDiv {α : Type*} [Fintype α] (hr : IsPowerBarrier ν c₁ c₂ r)
    {x y : α → ℝ} (hx : ∀ a, x a ∈ Ioo 0 1) (hy : ∀ a, y a ∈ Ioo 0 1) (hx1 : ∑ a, x a = 1)
    (hy1 : ∑ a, y a = 1) :
    c₁ / 4 * (∑ a, |y a - x a|) ^ 2 ≤ bregDiv (fun w : α → ℝ ↦ ∑ a, r (w a)) y x
      (∑ a, deriv r (x a) • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ) := by
  rw [bregDiv_sum_apply]
  set m : α → ℝ := fun a ↦ max (y a) (x a) with hm_def
  have hm : ∀ a ∈ Finset.univ, 0 < m a := fun a _ ↦ lt_max_of_lt_left (hy a).1
  have hm1 : 1 ≤ ∑ a, m a :=
    hx1 ▸ Finset.sum_le_sum fun a _ ↦ le_max_right (y a) (x a)
  have hm2 : ∑ a, m a ≤ 2 := by
    calc ∑ a, m a ≤ ∑ a, (y a + x a) :=
          Finset.sum_le_sum fun a _ ↦ max_le (by linarith [(hx a).1]) (by linarith [(hy a).1])
      _ = 2 := by rw [Finset.sum_add_distrib, hx1, hy1]; norm_num
  have hCS := Finset.sq_sum_div_le_sum_sq_div Finset.univ (fun a ↦ |y a - x a|) hm
  have h1 : (∑ a, |y a - x a|) ^ 2 / 2 ≤ (∑ a, |y a - x a|) ^ 2 / ∑ a, m a :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) hm2
  have h2 : ∀ a, c₁ / 2 * ((y a - x a) ^ 2 / m a) ≤
      r (y a) - r (x a) - deriv r (x a) * (y a - x a) := fun a ↦ by
      have := hr.mul_sq_div_max_le_sub_sub (hy a) (hx a)
      rw [hm_def]
      calc c₁ / 2 * ((y a - x a) ^ 2 / max (y a) (x a)) =
          c₁ * (y a - x a) ^ 2 / (2 * max (y a) (x a)) := by ring
        _ ≤ _ := this
  calc c₁ / 4 * (∑ a, |y a - x a|) ^ 2 = c₁ / 2 * ((∑ a, |y a - x a|) ^ 2 / 2) := by ring
    _ ≤ c₁ / 2 * ∑ a, |y a - x a| ^ 2 / m a :=
        mul_le_mul_of_nonneg_left (h1.trans hCS) (by linarith [hr.pos])
    _ = ∑ a, c₁ / 2 * ((y a - x a) ^ 2 / m a) := by
        rw [Finset.mul_sum]
        simp_rw [sq_abs]
    _ ≤ _ := Finset.sum_le_sum fun a _ ↦ h2 a

/-- The increments of the derivative of a power barrier: if `κ` bounds `r''` below on `[x, y]`,
then `κ (y - x) ≤ r' y - r' x`. -/
lemma mul_sub_le_deriv_sub (hr : IsPowerBarrier ν c₁ c₂ r) (hx : x ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1)
    (hxy : x ≤ y) (hκ : ∀ z ∈ Icc x y, κ ≤ deriv (deriv r) z) :
    κ * (y - x) ≤ deriv r y - deriv r x := by
  have hsub : Icc x y ⊆ Ioo 0 1 := Icc_subset_Ioo hx.1 hy.2
  refine (convex_Icc x y).mul_sub_le_image_sub_of_le_deriv (hr.continuousOn_deriv.mono hsub)
    (hr.differentiableOn_deriv.mono (interior_subset.trans hsub)) (fun z hz ↦ ?_) x
    ⟨le_rfl, hxy⟩ y ⟨hxy, le_rfl⟩ hxy
  exact hκ z (interior_subset hz)

/-- **The increments of the derivative of a power barrier with `ν > 1`** [SSKM26, Lemma 41],
corrected: for `0 < x ≤ y < 1`, `r' y - r' x ≥ c₁ / (ν - 1) * (x ^ (1 - ν) - y ^ (1 - ν))`.
[SSKM26] omits the factor `1 / (ν - 1)`. -/
lemma mul_rpow_sub_rpow_le_deriv_sub (hr : IsPowerBarrier ν c₁ c₂ r) (hν : 1 < ν)
    (hx : x ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1) (hxy : x ≤ y) :
    c₁ / (ν - 1) * (x ^ (1 - ν) - y ^ (1 - ν)) ≤ deriv r y - deriv r x := by
  have hν' : (ν - 1) ≠ 0 := (sub_pos.mpr hν).ne'
  have hmono : MonotoneOn (fun s ↦ deriv r s + c₁ / (ν - 1) * s ^ (1 - ν)) (Ioo 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo 0 1)
      (f' := fun s ↦ deriv (deriv r) s - c₁ / s ^ ν) ?_ (fun s hs ↦ ?_) (fun s hs ↦ ?_)
    · refine hr.continuousOn_deriv.add (ContinuousOn.mul continuousOn_const ?_)
      exact fun s hs ↦ (continuousAt_rpow_const _ _ (Or.inl hs.1.ne')).continuousWithinAt
    · rw [interior_Ioo] at hs ⊢
      have h := (hr.hasDerivAt_deriv hs).add
        ((hasDerivAt_rpow_const (p := 1 - ν) (Or.inl hs.1.ne')).const_mul (c₁ / (ν - 1)))
      convert h.hasDerivWithinAt using 1
      rw [show 1 - ν - 1 = -ν by ring, rpow_neg hs.1.le]
      field_simp
      ring
    · rw [interior_Ioo] at hs
      exact sub_nonneg.mpr (hr.le_deriv_deriv s hs)
  have h := hmono hx hy hxy
  simp only at h
  linarith [show c₁ / (ν - 1) * (x ^ (1 - ν) - y ^ (1 - ν)) =
    c₁ / (ν - 1) * x ^ (1 - ν) - c₁ / (ν - 1) * y ^ (1 - ν) by ring]

/-- **The increments of the derivative of a power barrier with `ν = 1`**: for `0 < x ≤ y < 1`,
`r' y - r' x ≥ c₁ log (y / x)`, the limit of `mul_rpow_sub_rpow_le_deriv_sub` as `ν → 1`. -/
lemma mul_log_div_le_deriv_sub (hr : IsPowerBarrier 1 c₁ c₂ r) (hx : x ∈ Ioo 0 1)
    (hy : y ∈ Ioo 0 1) (hxy : x ≤ y) :
    c₁ * log (y / x) ≤ deriv r y - deriv r x := by
  have hmono : MonotoneOn (fun s ↦ deriv r s - c₁ * log s) (Ioo 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo 0 1)
      (f' := fun s ↦ deriv (deriv r) s - c₁ * s⁻¹) ?_ (fun s hs ↦ ?_) (fun s hs ↦ ?_)
    · exact hr.continuousOn_deriv.sub (continuousOn_const.mul
        (continuousOn_log.mono fun s hs ↦ hs.1.ne'))
    · rw [interior_Ioo] at hs ⊢
      exact ((hr.hasDerivAt_deriv hs).sub
        ((hasDerivAt_log hs.1.ne').const_mul c₁)).hasDerivWithinAt
    · rw [interior_Ioo] at hs
      have h := hr.le_deriv_deriv s hs
      rw [rpow_one, div_eq_mul_inv] at h
      linarith
  have h := hmono hx hy hxy
  simp only at h
  rw [log_div hy.1.ne' hx.1.ne']
  linarith

end IsPowerBarrier

/-- The function `x ↦ x log x` is a power barrier with exponent `1` and constants `1, 1`: the
negative entropy [SSKM26, Section 2]. -/
lemma isPowerBarrier_mul_log : IsPowerBarrier 1 1 1 (fun x ↦ x * log x) := by
  set r : ℝ → ℝ := fun x ↦ x * log x with hr
  have h1 : ∀ x : ℝ, 0 < x → HasDerivAt r (log x + 1) x := fun x hx ↦
    hasDerivAt_mul_log hx.ne'
  have hderiv : ∀ x : ℝ, 0 < x → deriv r =ᶠ[nhds x] fun y ↦ log y + 1 := fun x hx ↦
    (eventually_gt_nhds hx).mono fun y hy ↦ (h1 y hy).deriv
  have h2 : ∀ x : ℝ, 0 < x → HasDerivAt (deriv r) x⁻¹ x := fun x hx ↦
    ((hasDerivAt_log hx.ne').add_const 1).congr_of_eventuallyEq (hderiv x hx)
  have hval : ∀ x : ℝ, x⁻¹ = 1 / x ^ (1 : ℝ) := fun x ↦ by rw [rpow_one, one_div]
  refine ⟨le_rfl, one_pos, fun x hx ↦ (h1 x hx.1).differentiableAt.differentiableWithinAt,
    fun x hx ↦ (h2 x hx.1).differentiableAt.differentiableWithinAt, fun x hx ↦ ?_,
    fun x hx ↦ ?_⟩
  · rw [(h2 x hx.1).deriv, hval]
  · rw [(h2 x hx.1).deriv, hval]

/-- The **Tsallis entropy** `(x - x ^ q) / (1 - q)` of index `q ∈ (0, 1)` is a power barrier with
exponent `2 - q` and constants `q, q` [SSKM26, Section 2]. -/
lemma isPowerBarrier_tsallis {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    IsPowerBarrier (2 - q) q q (fun x ↦ (x - x ^ q) / (1 - q)) := by
  set r : ℝ → ℝ := fun x ↦ (x - x ^ q) / (1 - q) with hr
  set r' : ℝ → ℝ := fun x ↦ (1 - q * x ^ (q - 1)) / (1 - q) with hr'
  have h1 : ∀ x : ℝ, 0 < x → HasDerivAt r (r' x) x := fun x hx ↦
    ((hasDerivAt_id x).sub (hasDerivAt_rpow_const (p := q) (Or.inl hx.ne'))).div_const (1 - q)
  have h2 : ∀ x : ℝ, 0 < x → HasDerivAt r' (q * x ^ (q - 2)) x := fun x hx ↦ by
    have := (((hasDerivAt_rpow_const (p := q - 1) (Or.inl hx.ne')).const_mul q).const_sub
      1).div_const (1 - q)
    convert this using 1
    rw [show q - 1 - 1 = q - 2 by ring]
    have : 1 - q ≠ 0 := by linarith
    field_simp
    ring
  have hderiv : ∀ x : ℝ, 0 < x → deriv r =ᶠ[nhds x] r' := fun x hx ↦
    (eventually_gt_nhds hx).mono fun y hy ↦ (h1 y hy).deriv
  have h2' : ∀ x : ℝ, 0 < x → HasDerivAt (deriv r) (q * x ^ (q - 2)) x := fun x hx ↦
    (h2 x hx).congr_of_eventuallyEq (hderiv x hx)
  have hval : ∀ x : ℝ, 0 < x → q * x ^ (q - 2) = q / x ^ (2 - q) := fun x hx ↦ by
    rw [show q - 2 = -(2 - q) by ring, rpow_neg hx.le, div_eq_mul_inv]
  refine ⟨by linarith, hq0, fun x hx ↦ (h1 x hx.1).differentiableAt.differentiableWithinAt,
    fun x hx ↦ (h2' x hx.1).differentiableAt.differentiableWithinAt, fun x hx ↦ ?_,
    fun x hx ↦ ?_⟩
  · rw [(h2' x hx.1).deriv, hval x hx.1]
  · rw [(h2' x hx.1).deriv, hval x hx.1]

/-- The **log barrier** `x ↦ -log x` is a power barrier with exponent `2` and constants `1, 1`
[SSKM26, Section 2]. -/
lemma isPowerBarrier_neg_log : IsPowerBarrier 2 1 1 (fun x ↦ -log x) := by
  set r : ℝ → ℝ := fun x ↦ -log x with hr
  have h1 : ∀ x : ℝ, 0 < x → HasDerivAt r (-x⁻¹) x := fun x hx ↦
    (hasDerivAt_log hx.ne').neg
  have hderiv : ∀ x : ℝ, 0 < x → deriv r =ᶠ[nhds x] fun y ↦ -y⁻¹ := fun x hx ↦
    (eventually_gt_nhds hx).mono fun y hy ↦ (h1 y hy).deriv
  have h2 : ∀ x : ℝ, 0 < x → HasDerivAt (deriv r) (1 / x ^ (2 : ℝ)) x := fun x hx ↦ by
    have := ((hasDerivAt_inv hx.ne').neg).congr_of_eventuallyEq (hderiv x hx)
    convert this using 1
    rw [rpow_two, neg_neg, one_div]
  refine ⟨by norm_num, one_pos, fun x hx ↦ (h1 x hx.1).differentiableAt.differentiableWithinAt,
    fun x hx ↦ (h2 x hx.1).differentiableAt.differentiableWithinAt, fun x hx ↦ ?_,
    fun x hx ↦ ?_⟩
  · rw [(h2 x hx.1).deriv]
  · rw [(h2 x hx.1).deriv]

end LMLExplore
