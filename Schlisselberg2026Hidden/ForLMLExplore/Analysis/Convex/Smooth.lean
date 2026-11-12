/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Bregman.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The descent lemma

Let `f` be a function on a convex set `K` of a real normed space `E` whose derivative is
`s`-Lipschitz on `K`, from the norm of `E` to the dual norm: `‖f' x - f' y‖ ≤ s ‖x - y‖`. Then
the first-order Taylor expansion of `f` at a point of `K` is accurate up to a quadratic term: for
`x, y ∈ K`, the Bregman divergence `D_f(y, x) = f y - f x - f' x (y - x)` satisfies
`|D_f(y, x)| ≤ s / 2 * ‖y - x‖ ^ 2`. Its upper half is the **descent lemma** of smooth
optimization.

Smoothness is usually defined through a derivative on an open set containing `K`. Here the
derivative is only asked to be a derivative within `K` at the points of `K`, which covers sets with
empty interior, such as the simplex in `α → ℝ`; the usual form follows
(`abs_bregDiv_fderiv_le_mul_norm_sub_sq`).

## Main statements

* `Convex.abs_bregDiv_le_mul_norm_sub_sq`: `|D_f(y, x)| ≤ s / 2 * ‖y - x‖ ^ 2` for a function with
  an `s`-Lipschitz derivative within a convex set `K`, at points of `K`.
* `Convex.bregDiv_le_mul_norm_sub_sq`: the descent lemma, `D_f(y, x) ≤ s / 2 * ‖y - x‖ ^ 2`.
* `Convex.abs_bregDiv_fderiv_le_mul_norm_sub_sq`: the same bound for a function differentiable on
  an open set containing `K`, with `fderiv`.
-/

public section

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {f : E → ℝ}
  {f' : E → E →L[ℝ] ℝ} {s : ℝ} {x y : E}

namespace Convex

/-- **Two-sided descent lemma.** Let `K` be convex and let `f` have a derivative `f' z` within `K`
at every `z ∈ K`, with `‖f' z - f' z'‖ ≤ s ‖z - z'‖` for `z, z' ∈ K`. Then for `x, y ∈ K`, the
Bregman divergence `D_f(y, x) = f y - f x - f' x (y - x)` satisfies
`|D_f(y, x)| ≤ s / 2 * ‖y - x‖ ^ 2`. -/
lemma abs_bregDiv_le_mul_norm_sub_sq (hK : Convex ℝ K)
    (hf : ∀ z ∈ K, HasFDerivWithinAt f (f' z) K z)
    (hf' : ∀ z ∈ K, ∀ z' ∈ K, ‖f' z - f' z'‖ ≤ s * ‖z - z'‖) (hx : x ∈ K) (hy : y ∈ K) :
    |bregDiv f y x (f' x)| ≤ s / 2 * ‖y - x‖ ^ 2 := by
  -- restrict `f` to the segment `ℓ t = x + t • (y - x)`, `t ∈ [0, 1]`
  set v := y - x with hv
  set ℓ : ℝ → E := fun t ↦ x + t • v with hℓ_def
  have hmaps : MapsTo ℓ (Icc 0 1) K := by
    intro t ht
    have := hK.mapsTo_lineMap hx hy ht
    rwa [AffineMap.lineMap_apply_module', add_comm] at this
  have hℓ (t : ℝ) : HasDerivAt ℓ v t := by
    convert ((hasDerivAt_id t).smul_const v).const_add x using 1
    · rfl
    · simp
  -- the remainder `g t = f (ℓ t) - f x - t f' x v` has derivative `(f' (ℓ t) - f' x) v`
  set g : ℝ → ℝ := fun t ↦ f (ℓ t) - f x - t * f' x v with hg_def
  have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt g (f' (ℓ t) v - f' x v) (Icc 0 1) t := by
    have h1 : HasDerivWithinAt (f ∘ ℓ) (f' (ℓ t) v) (Icc 0 1) t :=
      (hf (ℓ t) (hmaps ht)).comp_hasDerivWithinAt t (hℓ t).hasDerivWithinAt hmaps
    have h2 := ((hasDerivAt_id t).mul_const (f' x v)).hasDerivWithinAt (s := Icc 0 1)
    convert (h1.sub_const (f x)).sub h2 using 1
    · funext r
      simp [hg_def]
    · ring
  have hg_cont : ContinuousOn g (Icc 0 1) := fun t ht ↦ (hg t ht).continuousWithinAt
  have hg_right (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      HasDerivWithinAt g (f' (ℓ t) v - f' x v) (Ici t) t :=
    (hg t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))
  -- the derivative of the remainder is at most `s t ‖v‖²` in absolute value
  have h_bound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖f' (ℓ t) v - f' x v‖ ≤ s * t * ‖v‖ ^ 2 := by
    rw [← sub_apply]
    calc ‖(f' (ℓ t) - f' x) v‖
    _ ≤ ‖f' (ℓ t) - f' x‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ s * ‖ℓ t - x‖ * ‖v‖ :=
      mul_le_mul_of_nonneg_right (hf' _ (hmaps (Ico_subset_Icc_self ht)) _ hx) (norm_nonneg v)
    _ = s * t * ‖v‖ ^ 2 := by
      simp only [hℓ_def, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      ring
  have hB (t : ℝ) : HasDerivAt (fun t ↦ s / 2 * t ^ 2 * ‖v‖ ^ 2) (s * t * ‖v‖ ^ 2) t := by
    convert ((hasDerivAt_pow 2 t).const_mul (s / 2)).mul_const (‖v‖ ^ 2) using 1
    ring
  have h_main := image_norm_le_of_norm_deriv_right_le_deriv_boundary hg_cont hg_right
    (by simp [hg_def, hℓ_def]) hB h_bound (right_mem_Icc.mpr zero_le_one)
  have h_one : g 1 = bregDiv f y x (f' x) := by
    simp [hg_def, hℓ_def, hv, bregDiv]
  rwa [h_one, Real.norm_eq_abs, one_pow, mul_one] at h_main

/-- **The descent lemma.** Let `K` be convex and let `f` have a derivative `f' z` within `K` at
every `z ∈ K`, with `‖f' z - f' z'‖ ≤ s ‖z - z'‖` for `z, z' ∈ K`. Then for `x, y ∈ K`,
`f y ≤ f x + f' x (y - x) + s / 2 * ‖y - x‖ ^ 2`, in the form
`D_f(y, x) ≤ s / 2 * ‖y - x‖ ^ 2` of the Bregman divergence. -/
lemma bregDiv_le_mul_norm_sub_sq (hK : Convex ℝ K)
    (hf : ∀ z ∈ K, HasFDerivWithinAt f (f' z) K z)
    (hf' : ∀ z ∈ K, ∀ z' ∈ K, ‖f' z - f' z'‖ ≤ s * ‖z - z'‖) (hx : x ∈ K) (hy : y ∈ K) :
    bregDiv f y x (f' x) ≤ s / 2 * ‖y - x‖ ^ 2 :=
  (le_abs_self _).trans (hK.abs_bregDiv_le_mul_norm_sub_sq hf hf' hx hy)

/-- **Two-sided descent lemma, for a derivative on an open set.** Let `K` be convex and let `f` be
differentiable on an open set `U ⊇ K`, with `‖f' z - f' z'‖ ≤ s ‖z - z'‖` for `z, z' ∈ K`, where
`f' = fderiv ℝ f`. Then for `x, y ∈ K`, `|D_f(y, x)| ≤ s / 2 * ‖y - x‖ ^ 2`. -/
lemma abs_bregDiv_fderiv_le_mul_norm_sub_sq (hK : Convex ℝ K) {U : Set E} (hU : IsOpen U)
    (hKU : K ⊆ U) (hf : DifferentiableOn ℝ f U)
    (hf' : ∀ z ∈ K, ∀ z' ∈ K, ‖fderiv ℝ f z - fderiv ℝ f z'‖ ≤ s * ‖z - z'‖) (hx : x ∈ K)
    (hy : y ∈ K) :
    |bregDiv f y x (fderiv ℝ f x)| ≤ s / 2 * ‖y - x‖ ^ 2 :=
  hK.abs_bregDiv_le_mul_norm_sub_sq
    (fun z hz ↦ ((hf z (hKU hz)).differentiableAt (hU.mem_nhds (hKU hz))).hasFDerivAt
      |>.hasFDerivWithinAt) hf' hx hy

end Convex
