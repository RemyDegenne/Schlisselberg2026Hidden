/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Mathlib.Analysis.Real.Sqrt

/-!
# A bound on the roots of a quadratic

If `a > 0`, `b, c ≥ 0` and `a x² ≤ b x + c`, then `x ≤ b / a + √(c / a)`: the largest root
`(b + √(b² + 4 a c)) / (2 a)` of `a x² - b x - c` is at most `b / a + √(c / a)`. The inequality is
strict when `b, c > 0` [SSKM26, Lemma 23]. A quadratic inequality of this form appears when a
distance `x` is bounded through a strong convexity lower bound `a x²` on one side and a linear
upper bound `b x + c` on the other, as in the stability of approximate follow the regularized
leader (Lemma 51 of [SSKM26]).

## Main statements

* `Real.le_div_add_sqrt_div_of_mul_sq_le`: [SSKM26, Lemma 23], non-strict form for `b, c ≥ 0`.
* `Real.lt_div_add_sqrt_div_of_mul_sq_le`: [SSKM26, Lemma 23], for `b, c > 0`.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

public section

namespace Real

variable {a b c x : ℝ}

/-- **A bound on the roots of a quadratic** [SSKM26, Lemma 23], non-strict form. If `a > 0`,
`b, c ≥ 0` and `a x² ≤ b x + c`, then `x ≤ b / a + √(c / a)`. -/
lemma le_div_add_sqrt_div_of_mul_sq_le (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a * x ^ 2 ≤ b * x + c) : x ≤ b / a + √(c / a) := by
  set s := √(c / a) with hs_def
  have hs : 0 ≤ s := sqrt_nonneg _
  have has : a * s ^ 2 = c := by
    rw [hs_def, sq_sqrt (div_nonneg hc ha.le)]
    field_simp
  refine le_of_not_gt fun hlt ↦ ?_
  -- `a x - b > a s ≥ 0` and `x > s ≥ 0`, so `a x² - b x = x (a x - b) > s (a s) = c`
  have hx : b + a * s < a * x := by
    have := mul_lt_mul_of_pos_left hlt ha
    rwa [mul_add, mul_div_cancel₀ _ ha.ne'] at this
  have hbx : 0 ≤ b / a := div_nonneg hb ha.le
  have hsx : s < x := by linarith
  nlinarith [mul_nonneg ha.le hs]

/-- **A bound on the roots of a quadratic** [SSKM26, Lemma 23]. If `a, b, c > 0` and
`a x² - b x - c ≤ 0`, then `x < b / a + √(c / a)`. -/
lemma lt_div_add_sqrt_div_of_mul_sq_le (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * x ^ 2 ≤ b * x + c) : x < b / a + √(c / a) := by
  set s := √(c / a) with hs_def
  have hs : 0 < s := sqrt_pos.mpr (div_pos hc ha)
  have has : a * s ^ 2 = c := by
    rw [hs_def, sq_sqrt (div_pos hc ha).le]
    field_simp
  refine lt_of_not_ge fun hlt ↦ ?_
  -- `a x - b ≥ a s > 0` and `x > s > 0`, so `a x² - b x = x (a x - b) > s (a s) = c`
  have hx : b + a * s ≤ a * x := by
    have := mul_le_mul_of_nonneg_left hlt ha.le
    rwa [mul_add, mul_div_cancel₀ _ ha.ne'] at this
  have hsx : s < x := by linarith [div_pos hb ha]
  nlinarith [mul_pos ha hs]

end Real
