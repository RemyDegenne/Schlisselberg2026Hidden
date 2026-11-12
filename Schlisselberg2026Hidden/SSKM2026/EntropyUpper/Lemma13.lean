/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Lemma 13 of [SSKM26] for the negative entropy: from the balance to the weights

For the negative entropy, the balance of the arms `j` and `i` between two rounds `s` and `t` of
a trajectory `a` is `(log (a s j) - log (a t j)) + (log (a t i) - log (a s i))`. If it is at most
`K` and the weight of `i` did not decrease, then the weight of `j` did not decrease by more than
the factor `e^K`; if the weight of `j` did not increase, then the weight of `i` did not increase by
more than `e^K` [SSKM26, Lemma 13]. This file states it for four positive numbers
`x = a s j`, `y = a t j`, `z = a s i`, `w = a t i`.

## Main statements

* `Schlisselberg2026Hidden.le_exp_mul_of_log_sub_log_add_le`,
  `Schlisselberg2026Hidden.le_exp_mul_of_log_sub_log_add_le'`: [SSKM26, Lemma 13], for the
  negative entropy.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open Real

namespace Schlisselberg2026Hidden

variable {x y z w K : ℝ}

/-- **From the balance to the weights** [SSKM26, Lemma 13], first part, for the negative
entropy. For positive `x, y, z, w` with `z ≤ w`, if
`(log x - log y) + (log w - log z) ≤ K`, then `x ≤ e^K y`. -/
lemma le_exp_mul_of_log_sub_log_add_le (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hzw : z ≤ w)
    (h : log x - log y + (log w - log z) ≤ K) : x ≤ exp K * y := by
  have h1 : log z ≤ log w := log_le_log hz hzw
  calc x = exp (log x) := (exp_log hx).symm
    _ ≤ exp (K + log y) := exp_le_exp.2 (by linarith)
    _ = exp K * y := by rw [exp_add, exp_log hy]

/-- **From the balance to the weights** [SSKM26, Lemma 13], second part, for the negative
entropy. For positive `x, y, z, w` with `y ≤ x`, if
`(log x - log y) + (log w - log z) ≤ K`, then `w ≤ e^K z`. -/
lemma le_exp_mul_of_log_sub_log_add_le' (hy : 0 < y) (hz : 0 < z) (hw : 0 < w) (hyx : y ≤ x)
    (h : log x - log y + (log w - log z) ≤ K) : w ≤ exp K * z := by
  have h1 : log y ≤ log x := log_le_log hy hyx
  calc w = exp (log w) := (exp_log hw).symm
    _ ≤ exp (K + log z) := exp_le_exp.2 (by linarith)
    _ = exp K * z := by rw [exp_add, exp_log hz]

end Schlisselberg2026Hidden
