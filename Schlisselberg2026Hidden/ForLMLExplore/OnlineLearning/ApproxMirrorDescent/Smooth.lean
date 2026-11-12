/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Analysis.Convex.Bregman.StrongConvex
public import Schlisselberg2026Hidden.ForLMLExplore.Analysis.Convex.ApproxMinimizer
public import Schlisselberg2026Hidden.ForLMLExplore.Analysis.Convex.Smooth
public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent

/-!
# Approximate mirror descent with a smooth potential

Let `K` be a convex set of diameter at most `D` in a real normed space, and let the potential `F`
have a derivative `F' z` within `K` at every `z ∈ K` that is `β`-Lipschitz on `K` from the norm to
the dual norm. The one-step inequality of exact mirror descent,
`η y (x - u) ≤ D_F(u, a) - D_F(u, x) - D_F(x, a)`, comes from the first-order optimality condition
of the step `x`. For an `ε`-approximate step, the approximate first-order condition of an
`ε`-minimizer of a smooth function (`neg_mul_sqrt_le_apply_sub_of_le_add`) gives it up to the
additive error `D √(2 β ε)`. Summed over the rounds, the regret of an approximate trajectory with
errors `ε t` exceeds the bound of exact mirror descent by `D ∑ t, √(2 β ε t) / η`
[SSKM26, Theorem 2].

## Main statements

* `IsApproxMirrorDescentStep.mul_apply_sub_le_of_smooth`: [SSKM26, proof of Theorem 2], the
  one-step inequality for `ε ≤ β D² / 2`.
* `IsApproxMirrorDescentStep.mul_apply_sub_le_of_strongConvexOn`: the same for an `m`-strongly
  convex potential and `ε ≤ m D² / 2`.
* `approxMirrorDescent_sum_apply_sub_le`: [SSKM26, Theorem 2], for an `m`-strongly convex
  potential, per-round errors `ε t ≤ m D² / 2` and any losses:
  `∑ t < n, y t (a t - u) ≤ D_F(u, a 0) / η + η / (2 m) ∑ t < n, ‖y t‖ ^ 2
    + D ∑ t < n, √(2 β ε t) / η`.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

public section

open Finset

namespace LMLExplore.OnlineLearning

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {F : E → ℝ}
  {F' : E → E →L[ℝ] ℝ} {η β D m ε : ℝ} {y J : E →L[ℝ] ℝ} {a x u : E}

/-- **One step of approximate mirror descent with a smooth potential** [SSKM26, proof of
Theorem 2]. Let `K` be convex with `‖z - z'‖ ≤ D` on `K`, and let `F` have a derivative `F' z`
within `K` at every `z ∈ K` with `‖F' z - F' z'‖ ≤ β ‖z - z'‖`. If `x` is an `ε`-approximate
mirror descent step on `K` from `a`, with linear map `J`, and `ε ≤ β D² / 2`, then for every
`u ∈ K`, `η y (x - u) ≤ D_F(u, a) - D_F(u, x) - D_F(x, a) + D √(2 β ε)`, where the divergences
from `a` use `J` and the divergence from `x` uses `F' x`. Neither `a ∈ K` nor `η > 0` is needed,
and `J` need not be a derivative of `F` at `a`. -/
lemma IsApproxMirrorDescentStep.mul_apply_sub_le_of_smooth
    (h : IsApproxMirrorDescentStep K F η y a J ε x) (hK : Convex ℝ K)
    (hF : ∀ z ∈ K, HasFDerivWithinAt F (F' z) K z)
    (hβ : ∀ z ∈ K, ∀ z' ∈ K, ‖F' z - F' z'‖ ≤ β * ‖z - z'‖)
    (hD : ∀ z ∈ K, ∀ z' ∈ K, ‖z - z'‖ ≤ D) (hεD : ε ≤ β * D ^ 2 / 2) (hu : u ∈ K) :
    η * y (x - u) ≤
      bregDiv F u a J - bregDiv F u x (F' x) - bregDiv F x a J + D * √(2 * β * ε) := by
  have hx := h.mem
  -- the objective `φ` of the step is `ε`-minimized at `x`, and its Bregman divergence from `x`,
  -- for the linear map `φ' = η y + F' x - J`, is that of `F`
  set φ : E → ℝ := fun b ↦ η * y b + bregDiv F b a J with hφ
  set φ' : E →L[ℝ] ℝ := η • y + F' x - J with hφ'
  have hmin (z : E) (hz : z ∈ segment ℝ x u) : φ x ≤ φ z + ε :=
    h.le_add z (hK.segment_subset hx hu hz)
  have hquad (z : E) (hz : z ∈ segment ℝ x u) : bregDiv φ z x φ' ≤ β / 2 * ‖z - x‖ ^ 2 := by
    have h_eq : bregDiv φ z x φ' = bregDiv F z x (F' x) := by
      simp only [hφ, hφ', bregDiv, add_apply, sub_apply, smul_apply, smul_eq_mul, map_sub]
      ring
    rw [h_eq]
    exact hK.bregDiv_le_mul_norm_sub_sq hF hβ hx (hK.segment_subset hx hu hz)
  have h_first := neg_mul_sqrt_le_apply_sub_of_le_add (hD u hu x hx) hεD hmin hquad
  -- the three-point identity `D_F(u, x) + D_F(x, a) - D_F(u, a) = (J - F' x) (u - x)`
  have h_three := bregDiv_three_point (f := F) (z := u) (x := x) (y := a) (J_x := F' x) (J_y := J)
  simp only [hφ', add_apply, sub_apply, smul_apply, smul_eq_mul, map_sub] at h_first h_three ⊢
  linarith

/-- **One step of approximate mirror descent with a smooth, strongly convex potential.** Under
the assumptions of `IsApproxMirrorDescentStep.mul_apply_sub_le_of_smooth`, with `F` `m`-strongly
convex on `K` and `ε ≤ m D² / 2` in place of `ε ≤ β D² / 2`, the same inequality holds: when `K`
has two points, `m ≤ β`. -/
lemma IsApproxMirrorDescentStep.mul_apply_sub_le_of_strongConvexOn
    (h : IsApproxMirrorDescentStep K F η y a J ε x) (hK : Convex ℝ K)
    (hF : ∀ z ∈ K, HasFDerivWithinAt F (F' z) K z) (hFm : StrongConvexOn K m F)
    (hβ : ∀ z ∈ K, ∀ z' ∈ K, ‖F' z - F' z'‖ ≤ β * ‖z - z'‖)
    (hD : ∀ z ∈ K, ∀ z' ∈ K, ‖z - z'‖ ≤ D) (hεD : ε ≤ m * D ^ 2 / 2) (hu : u ∈ K) :
    η * y (x - u) ≤
      bregDiv F u a J - bregDiv F u x (F' x) - bregDiv F x a J + D * √(2 * β * ε) := by
  have hx := h.mem
  rcases eq_or_ne u x with rfl | hux
  · have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD u hu u hu)
    simp only [sub_self, map_zero, mul_zero, bregDiv_self]
    linarith [mul_nonneg hD0 (Real.sqrt_nonneg (2 * β * ε))]
  -- `m / 2 ‖u - x‖² ≤ D_F(u, x) ≤ β / 2 ‖u - x‖²` with `u ≠ x`, so `m ≤ β`
  have hpos : 0 < ‖u - x‖ ^ 2 := by
    have : 0 < ‖u - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hux)
    positivity
  have h_lower := hFm.mul_norm_sub_sq_le_bregDiv hx hu (hF x hx)
  have h_upper := hK.bregDiv_le_mul_norm_sub_sq hF hβ hx hu
  have hmβ : m ≤ β := by nlinarith
  refine h.mul_apply_sub_le_of_smooth hK hF hβ hD (hεD.trans ?_) hu
  have := sq_nonneg D
  nlinarith

/-- **Regret of approximate mirror descent with a smooth, strongly convex potential**
[SSKM26, Theorem 2]. Let `K` be convex with `‖z - z'‖ ≤ D` on `K`, and let `F` have a derivative
`F' z` within `K` at every `z ∈ K`, be `m`-strongly convex on `K` with `m > 0`, and satisfy
`‖F' z - F' z'‖ ≤ β ‖z - z'‖` on `K`. Let `η > 0`, `a 0 ∈ K`, and let each `a (t + 1)`, for
`t < n`, be an `ε t`-approximate mirror descent step on `K` from `a t` with derivative
`F' (a t)`, for the loss `y t`, with `ε t ≤ m D² / 2`. Then for every `u ∈ K`,
`∑ t < n, y t (a t - u) ≤ D_F(u, a 0) / η + η / (2 m) ∑ t < n, ‖y t‖ ^ 2
  + D ∑ t < n, √(2 β ε t) / η`,
where `‖y t‖` is the dual norm of the loss.

The paper states the case `m = 1`, `‖y t‖ ≤ 1` and `ε t = ε`, with `O(·)`. -/
lemma approxMirrorDescent_sum_apply_sub_le (hK : Convex ℝ K)
    (hF : ∀ z ∈ K, HasFDerivWithinAt F (F' z) K z) (hFm : StrongConvexOn K m F) (hm : 0 < m)
    (hβ : ∀ z ∈ K, ∀ z' ∈ K, ‖F' z - F' z'‖ ≤ β * ‖z - z'‖)
    (hD : ∀ z ∈ K, ∀ z' ∈ K, ‖z - z'‖ ≤ D) (hη : 0 < η) {n : ℕ} (y : ℕ → E →L[ℝ] ℝ)
    (ε : ℕ → ℝ) (hεD : ∀ t < n, ε t ≤ m * D ^ 2 / 2) (a : ℕ → E) (ha0 : a 0 ∈ K)
    (ha : ∀ t < n, IsApproxMirrorDescentStep K F η (y t) (a t) (F' (a t)) (ε t) (a (t + 1)))
    (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤ bregDiv F u (a 0) (F' (a 0)) / η +
      η / (2 * m) * ∑ t ∈ range n, ‖y t‖ ^ 2 + D * (∑ t ∈ range n, √(2 * β * ε t)) / η := by
  have hmem : ∀ t ≤ n, a t ∈ K
    | 0, _ => ha0
    | t + 1, ht => (ha t ht).mem
  set d : ℕ → ℝ := fun t ↦ bregDiv F u (a t) (F' (a t)) with hd
  -- each round: the stability term, the telescoping divergences and the error of the step
  have h_round (t : ℕ) (ht : t ∈ range n) : y t (a t - u) ≤
      η / (2 * m) * ‖y t‖ ^ 2 + (d t - d (t + 1)) / η + D * √(2 * β * ε t) / η := by
    have ht' := mem_range.mp ht
    have h_step := (ha t ht').mul_apply_sub_le_of_strongConvexOn hK hF hFm hβ hD (hεD t ht') hu
    have h_stab := apply_sub_sub_div_le_of_mul_norm_sq_le hm hη (y t)
      (hFm.mul_norm_sub_sq_le_bregDiv (hmem t ht'.le) (hmem (t + 1) ht') (hF _ (hmem t ht'.le)))
    have h_split : y t (a t - u) = y t (a t - a (t + 1)) + y t (a (t + 1) - u) := by
      rw [← map_add, sub_add_sub_cancel]
    have h_div : y t (a (t + 1) - u) ≤ (d t - d (t + 1) -
        bregDiv F (a (t + 1)) (a t) (F' (a t)) + D * √(2 * β * ε t)) / η := by
      rw [le_div_iff₀ hη, mul_comm]
      exact h_step
    rw [h_split]
    have h_eq : (d t - d (t + 1) - bregDiv F (a (t + 1)) (a t) (F' (a t)) +
        D * √(2 * β * ε t)) / η = (d t - d (t + 1)) / η + D * √(2 * β * ε t) / η -
          bregDiv F (a (t + 1)) (a t) (F' (a t)) / η := by
      ring
    linarith
  -- the last divergence `D_F(u, a n)` is nonnegative
  have h_last : 0 ≤ d n / η := by
    refine div_nonneg ((by positivity : 0 ≤ m / 2 * ‖u - a n‖ ^ 2).trans ?_) hη.le
    exact hFm.mul_norm_sub_sq_le_bregDiv (hmem n le_rfl) hu (hF _ (hmem n le_rfl))
  have h_tele : ∑ t ∈ range n, (d t - d (t + 1)) / η = d 0 / η - d n / η := by
    rw [← sum_div, sum_range_sub', sub_div]
  calc ∑ t ∈ range n, y t (a t - u)
  _ ≤ ∑ t ∈ range n,
      (η / (2 * m) * ‖y t‖ ^ 2 + (d t - d (t + 1)) / η + D * √(2 * β * ε t) / η) :=
    sum_le_sum h_round
  _ = η / (2 * m) * ∑ t ∈ range n, ‖y t‖ ^ 2 + (d 0 / η - d n / η) +
      D * (∑ t ∈ range n, √(2 * β * ε t)) / η := by
    have h1 : ∑ t ∈ range n, η / (2 * m) * ‖y t‖ ^ 2 =
        η / (2 * m) * ∑ t ∈ range n, ‖y t‖ ^ 2 := (mul_sum ..).symm
    have h2 : ∑ t ∈ range n, D * √(2 * β * ε t) / η =
        D * (∑ t ∈ range n, √(2 * β * ε t)) / η := by
      rw [mul_sum, sum_div]
    rw [sum_add_distrib, sum_add_distrib, h_tele, h1, h2]
  _ ≤ _ := by
    simp only [hd] at h_last ⊢
    linarith

end LMLExplore.OnlineLearning
