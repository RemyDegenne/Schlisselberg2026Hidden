/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Lemma 21 of [SSKM26] for the negative entropy: the scalar Bregman divergence

The Bregman divergence of the negative entropy `∑ i, (x i * log (x i) - x i)` between `x` and a
point `y` with positive coordinates is the sum over the coordinates of the scalar divergence
`x * log (x / y) - x + y`. This file gives the bounds on it that the analysis of the negative
entropy uses: it is nonnegative, at most the `χ²` term `(x - y) ^ 2 / y`, at least
`(y - x) ^ 2 / (2 y)` below `y`, and nondecreasing in `x` above `y`.

These are the bounds of Lemma 21 of [SSKM26] for `r x = x log x`, with the base point `y` in
place of the extreme values of `r''` on the segment: the `χ²` bound holds on the whole segment,
endpoints with zero coordinates included, which the paper's form does not give (its `β` is
infinite on a segment that reaches `0`).

## Main statements

* `Schlisselberg2026Hidden.mul_log_div_sub_add_nonneg`,
  `Schlisselberg2026Hidden.mul_log_div_sub_add_le_sq_div`,
  `Schlisselberg2026Hidden.sq_div_two_mul_le_mul_log_div_sub_add`: [SSKM26, Lemma 21], for the
  negative entropy.
* `Schlisselberg2026Hidden.mul_log_div_sub_add_le_of_le`: the divergence is nondecreasing in `x`
  on `[y, ∞)`.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open Real

namespace Schlisselberg2026Hidden

variable {x y z : ℝ}

/-- For `y ≠ 0`, `x * log (x / y) = x * log x - x * log y`, also for `x = 0`. -/
lemma mul_log_div_eq_sub (x : ℝ) (hy : y ≠ 0) : x * log (x / y) = x * log x - x * log y := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [log_div hx hy]
  ring

/-- **Nonnegativity of the scalar divergence** [SSKM26, Lemma 21]:
`0 ≤ x * log (x / y) - x + y` for `x ≥ 0` and `y > 0`. -/
lemma mul_log_div_sub_add_nonneg (hx : 0 ≤ x) (hy : 0 < y) : 0 ≤ x * log (x / y) - x + y := by
  rcases hx.eq_or_lt with rfl | hx
  · simpa using hy.le
  -- `log (x / y) ≥ 1 - y / x`
  have h := log_le_sub_one_of_pos (div_pos hy hx)
  rw [log_div hy.ne' hx.ne', ← neg_sub, ← log_div hx.ne' hy.ne'] at h
  have : x * (1 - y / x) ≤ x * log (x / y) := mul_le_mul_of_nonneg_left (by linarith) hx.le
  rw [mul_sub, mul_one, mul_div_cancel₀ _ hx.ne'] at this
  linarith

/-- **The `χ²` bound on the scalar divergence** [SSKM26, Lemma 21]:
`x * log (x / y) - x + y ≤ (x - y) ^ 2 / y` for `x ≥ 0` and `y > 0`. -/
lemma mul_log_div_sub_add_le_sq_div (hx : 0 ≤ x) (hy : 0 < y) :
    x * log (x / y) - x + y ≤ (x - y) ^ 2 / y := by
  have h : x * log (x / y) ≤ x * (x / y - 1) := by
    rcases hx.eq_or_lt with rfl | hx
    · simp
    exact mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (div_pos hx hy)) hx.le
  have : x * (x / y - 1) - x + y = (x - y) ^ 2 / y := by
    field_simp
    ring
  linarith

/-- On `[0, 1]`, `(1 - s) ^ 2 / 2 ≤ s * log s - s + 1`: the function
`s ↦ s log s - s + 1 - (1 - s) ^ 2 / 2` is nonincreasing, with value `0` at `1`. -/
lemma sq_one_sub_div_two_le_mul_log_sub_add_one {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) ^ 2 / 2 ≤ s * log s - s + 1 := by
  set g : ℝ → ℝ := fun s ↦ s * log s - s + 1 - (1 - s) ^ 2 / 2 with hg
  have hderiv (s : ℝ) (hs : s ≠ 0) : HasDerivAt g (log s + 1 - s) s := by
    have h1 := hasDerivAt_mul_log hs
    have h2 : HasDerivAt (fun s : ℝ ↦ (1 - s) ^ 2 / 2) (-(1 - s)) s :=
      ((((hasDerivAt_id s).const_sub 1).fun_pow 2).div_const 2).congr_deriv (by simp; ring)
    exact (((h1.fun_sub (hasDerivAt_id s)).add_const 1).fun_sub h2).congr_deriv (by ring)
  have h_anti : AntitoneOn g (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) ?_ ?_ ?_
    · refine Continuous.continuousOn ?_
      simp only [hg]
      fun_prop
    · intro s hs
      rw [interior_Icc] at hs
      exact (hderiv s hs.1.ne').differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hderiv s hs.1.ne').deriv]
      linarith [log_le_sub_one_of_pos hs.1]
  have := h_anti ⟨hs0, hs1⟩ ⟨zero_le_one, le_rfl⟩ hs1
  simp only [hg, log_one, mul_zero, sub_self, zero_sub, neg_add_cancel, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div] at this
  linarith

/-- **The lower bound on the scalar divergence** [SSKM26, Lemma 21]: for `0 ≤ x ≤ y` and
`y > 0`, `(y - x) ^ 2 / (2 y) ≤ x * log (x / y) - x + y`. -/
lemma sq_div_two_mul_le_mul_log_div_sub_add (hx : 0 ≤ x) (hxy : x ≤ y) (hy : 0 < y) :
    (y - x) ^ 2 / (2 * y) ≤ x * log (x / y) - x + y := by
  have h := sq_one_sub_div_two_le_mul_log_sub_add_one (div_nonneg hx hy.le)
    ((div_le_one hy).2 hxy)
  have h' := mul_le_mul_of_nonneg_left h hy.le
  have e1 : y * ((1 - x / y) ^ 2 / 2) = (y - x) ^ 2 / (2 * y) := by
    field_simp
  have e2 : y * (x / y * log (x / y) - x / y + 1) = x * log (x / y) - x + y := by
    field_simp
  rwa [e1, e2] at h'

/-- The scalar divergence `x ↦ x * log (x / y) - x + y` is nondecreasing on `[y, ∞)`. -/
lemma mul_log_div_sub_add_le_of_le (hy : 0 < y) (hyx : y ≤ x) (hxz : x ≤ z) :
    x * log (x / y) - x + y ≤ z * log (z / y) - z + y := by
  have hx : 0 < x := hy.trans_le hyx
  have hz : 0 < z := hx.trans_le hxz
  -- `z log (z / y) - x log (x / y) = z log (z / x) + (z - x) log (x / y)`, with
  -- `log (z / x) ≥ 1 - x / z` and `log (x / y) ≥ 0`
  have e : z * log (z / y) = z * log (z / x) + z * log (x / y) := by
    rw [← mul_add, ← log_mul (div_pos hz hx).ne' (div_pos hx hy).ne']
    congr 2
    field_simp
  have h1 : z * (1 - x / z) ≤ z * log (z / x) := by
    refine mul_le_mul_of_nonneg_left ?_ hz.le
    have := log_le_sub_one_of_pos (div_pos hx hz)
    rw [log_div hx.ne' hz.ne', ← neg_sub, ← log_div hz.ne' hx.ne'] at this
    linarith
  rw [mul_sub, mul_one, mul_div_cancel₀ _ hz.ne'] at h1
  have h2 : 0 ≤ (z - x) * log (x / y) :=
    mul_nonneg (by linarith) (log_nonneg ((one_le_div hy).2 hyx))
  nlinarith

end Schlisselberg2026Hidden
