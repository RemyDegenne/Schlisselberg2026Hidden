/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Analysis.Convex.NegEntropy

/-!
# The negative entropy on `α → ℝ`: derivative and Bregman divergence

LMLExplore's `LMLExplore.hasFDerivAt_negEntropy` and `LMLExplore.bregDiv_negEntropy` state the
derivative and the Bregman divergence of the negative entropy
`negEntropy x = ∑ a, (x a log x a - x a)` on `PiLp p (fun _ ↦ ℝ)`. This file states them on
`α → ℝ`, with the derivative `∑ a, log (x a) • ContinuousLinearMap.proj a`. The Bregman divergence
only evaluates the linear map, so it does not depend on the norm: on `α → ℝ` it is the relative
entropy on the simplex, and the generalized relative entropy
`∑ a, (x a log (x a / y a) - x a + y a)` in general.

## Main statements

* `LMLExplore.hasFDerivAt_negEntropy_pi`: the derivative of the negative entropy at a point with
  nonzero coordinates.
* `LMLExplore.bregDiv_negEntropy_pi_eq`: its Bregman divergence is the generalized relative entropy.
* `LMLExplore.bregDiv_negEntropy_pi`: on the simplex, its Bregman divergence is the relative
  entropy.
-/

@[expose] public section

open Real

namespace LMLExplore

variable {α : Type*} [Fintype α] {x y : α → ℝ}

/-- The derivative of the negative entropy on `α → ℝ`, at a point with nonzero coordinates, is the
linear map `h ↦ ∑ a, log (x a) * h a`. -/
lemma hasFDerivAt_negEntropy_pi (hx : ∀ a, x a ≠ 0) :
    HasFDerivAt negEntropy
      (∑ a, log (x a) • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ) x := by
  have h : negEntropy = fun x : α → ℝ ↦ ∑ a, (x a * log (x a) - x a) := funext negEntropy_def
  rw [h]
  have hA : ∀ a ∈ Finset.univ, HasFDerivAt (fun y : α → ℝ ↦ y a * log (y a) - y a)
      (log (x a) • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ) x := fun a _ ↦ by
    have hd : HasDerivAt (fun t ↦ t * log t - t) (log (x a)) (x a) := by
      convert (hasDerivAt_mul_log (hx a)).sub (hasDerivAt_id' (x a)) using 1
      ring
    exact hd.comp_hasFDerivAt x (hasFDerivAt_apply (𝕜 := ℝ) a x)
  exact HasFDerivAt.fun_sum hA

/-- The Bregman divergence of the negative entropy on `α → ℝ` is the generalized relative entropy
`∑ a, (x a log (x a / y a) - x a + y a)`, when `x` vanishes wherever `y` does. -/
lemma bregDiv_negEntropy_pi_eq (hxy : ∀ a, y a = 0 → x a = 0) :
    bregDiv negEntropy x y (∑ a, log (y a) • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ) =
      ∑ a, (x a * log (x a / y a) - x a + y a) := by
  simp only [bregDiv, negEntropy_def, sum_apply, smul_apply, ContinuousLinearMap.proj_apply,
    Pi.sub_apply, smul_eq_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases hx : x a = 0
  · simp only [hx, zero_div, log_zero, mul_zero, sub_zero, zero_sub]
    ring
  · have hy : y a ≠ 0 := fun h ↦ hx (hxy a h)
    rw [log_div hx hy]
    ring

/-- On the simplex, the Bregman divergence of the negative entropy on `α → ℝ` is the relative
entropy `∑ a, x a log (x a / y a)`, when `x` vanishes wherever `y` does. -/
lemma bregDiv_negEntropy_pi (hx : x ∈ simplex α) (hy : y ∈ simplex α)
    (hxy : ∀ a, y a = 0 → x a = 0) :
    bregDiv negEntropy x y (∑ a, log (y a) • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ) =
      ∑ a, x a * log (x a / y a) := by
  rw [bregDiv_negEntropy_pi_eq hxy, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    (mem_simplex_iff.mp hx).2, (mem_simplex_iff.mp hy).2]
  ring

end LMLExplore
