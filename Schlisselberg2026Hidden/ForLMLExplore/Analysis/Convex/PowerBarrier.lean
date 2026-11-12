/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
* `Convex.exists_mem_segment_sub_sub_mul_eq`: Taylor's formula of order two, for a real function
  with a derivative and a second derivative within a convex set.
* `LMLExplore.IsPowerBarrier.strictMonoOn_deriv`: the derivative of a power barrier is strictly
  monotone on `(0, 1)`.
* `LMLExplore.IsPowerBarrier.sub_sub_le_mul_sq`: the scalar Bregman divergence is at most
  `M (x - y) ^ 2 / 2` when `r'' ≤ M` between `x` and `y` [SSKM26, Lemma 21].
* `LMLExplore.IsPowerBarrier.sub_sub_nonneg`, `LMLExplore.IsPowerBarrier.mul_sq_le_sub_sub`,
  `LMLExplore.IsPowerBarrier.mul_sq_div_max_le_sub_sub`: the scalar Bregman divergence is
  nonnegative, and has quadratic lower bounds given by lower bounds on `r''`.
* `LMLExplore.IsPowerBarrier.mul_rpow_sub_rpow_le_deriv_sub`: the increments of `r'` for `ν > 1`
  [SSKM26, Lemma 41], with the factor `1 / (ν - 1)` that [SSKM26] omits.
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

end LMLExplore
