/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The constants of Theorem 6 of [SSKM26], corrected

The threshold of the corrected Theorem 6 of [SSKM26] is `ε ≤ η⁴ ψ^ν / (4^{ν+2} max (1, c₂))`.
For `0 < η ≤ 2` and `0 < ψ ≤ 1` it implies the four conditions that the proof uses:
- the per-round balance error `√(c₂ (ψ / 4)^{-ν} ε) + 4 ε / ψ` is at most `η`;
- `ε ≤ η ψ`, so that the error `2 ε / ψ` of the step towards the start is at most `2 η`;
- `c₂ (ψ / 2)^{-ν} ε ≤ η⁴ / 4` and `4 ε ≤ η²`, so that the error of the approximate first-order
  condition in a round is at most `η²`.

## Main statements

* `Schlisselberg2026Hidden.barrier_constants`: the four conditions.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open Real

namespace Schlisselberg2026Hidden

/-- **The constants of Theorem 6** of [SSKM26], corrected. If `1 ≤ ν`, `0 < c₂`, `0 < η ≤ 2`,
`0 < ψ ≤ 1`, `0 ≤ ε` and `ε ≤ η⁴ ψ^ν / (4^{ν+2} max (1, c₂))`, then
`√(c₂ / (ψ / 4)^ν ε) + 4 ε / ψ ≤ η`, `ε ≤ η ψ`, `c₂ / (ψ / 2)^ν ε ≤ η⁴ / 4` and `4 ε ≤ η²`. -/
lemma barrier_constants {ν c₂ η ψ ε : ℝ} (hν : 1 ≤ ν) (hc₂ : 0 < c₂) (hη : 0 < η)
    (hη2 : η ≤ 2) (hψ : 0 < ψ) (hψ1 : ψ ≤ 1) (hε0 : 0 ≤ ε)
    (hε : ε ≤ η ^ 4 * ψ ^ ν / (4 ^ (ν + 2) * max 1 c₂)) :
    √(c₂ / (ψ / 2 / 2) ^ ν * ε) + 2 * ε / (ψ / 2) ≤ η ∧ ε ≤ η * ψ ∧
      c₂ / (ψ / 2) ^ ν * ε ≤ η ^ 4 / 4 ∧ 4 * ε ≤ η ^ 2 := by
  set P := ψ ^ ν with hP
  set F := (4 : ℝ) ^ ν with hF
  set mx := max 1 c₂ with hmx
  have hP0 : 0 < P := rpow_pos_of_pos hψ ν
  have hPψ : P ≤ ψ := by
    have := rpow_le_rpow_of_exponent_ge hψ hψ1 hν
    rwa [rpow_one] at this
  have hF4 : 4 ≤ F := by
    have := rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hν
    rwa [rpow_one] at this
  have hF0 : 0 < F := by linarith
  have h2F : (2 : ℝ) ^ ν ≤ F := rpow_le_rpow (by norm_num) (by norm_num) (by linarith)
  have h2ν : 0 < (2 : ℝ) ^ ν := rpow_pos_of_pos (by norm_num) ν
  have hmx1 : 1 ≤ mx := le_max_left _ _
  have hmxc : c₂ ≤ mx := le_max_right _ _
  have hmx0 : 0 < mx := by linarith
  have h4 : (4 : ℝ) ^ (ν + 2) = F * 16 := by
    rw [rpow_add (by norm_num), rpow_two, hF]
    norm_num
  rw [h4] at hε
  have hq4 : (ψ / 2 / 2) ^ ν = P / F := by
    rw [show ψ / 2 / 2 = ψ / 4 by ring, div_rpow hψ.le (by norm_num)]
  have hq2 : (ψ / 2) ^ ν = P / 2 ^ ν := div_rpow hψ.le (by norm_num) ν
  -- `ε ≤ η⁴ ψ / 64`
  have hθψ : ε ≤ η ^ 4 * ψ / 64 := by
    refine hε.trans (div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hPψ (by positivity))
      (by norm_num) ?_)
    nlinarith
  have hη3 : η ^ 3 ≤ 8 := by
    have := pow_le_pow_left₀ hη.le hη2 3
    norm_num at this
    exact this
  have hη4 : η ^ 4 ≤ 8 * η := by nlinarith
  have hη2' : η ^ 2 ≤ 4 := by nlinarith
  have hη4' : η ^ 4 ≤ 4 * η ^ 2 := by
    have := mul_le_mul_of_nonneg_left hη2' (sq_nonneg η)
    linarith
  have hεηψ : ε ≤ η * ψ / 8 := by nlinarith
  -- `c₂ F / P ε ≤ η⁴ / 16`
  have hA : c₂ * F / P * ε ≤ η ^ 4 / 16 := by
    calc c₂ * F / P * ε ≤ c₂ * F / P * (η ^ 4 * P / (F * 16 * mx)) := by gcongr
      _ = η ^ 4 / 16 * (c₂ / mx) := by field_simp
      _ ≤ η ^ 4 / 16 * 1 := by gcongr; exact (div_le_one hmx0).mpr hmxc
      _ = η ^ 4 / 16 := mul_one _
  have hB : c₂ / (ψ / 2) ^ ν * ε ≤ c₂ * F / P * ε := by
    rw [hq2]
    have e : c₂ / (P / 2 ^ ν) = c₂ * 2 ^ ν / P := by field_simp
    rw [e]
    gcongr
  refine ⟨?_, by nlinarith, by linarith [pow_pos hη 4], by nlinarith⟩
  have hs : √(c₂ / (ψ / 2 / 2) ^ ν * ε) ≤ η / 2 := by
    rw [hq4, show c₂ / (P / F) * ε = c₂ * F / P * ε by field_simp]
    calc √(c₂ * F / P * ε) ≤ √((η ^ 2 / 4) ^ 2) := sqrt_le_sqrt (by nlinarith)
      _ = η ^ 2 / 4 := sqrt_sq (by positivity)
      _ ≤ η / 2 := by nlinarith
  have ht : 2 * ε / (ψ / 2) ≤ η / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

end Schlisselberg2026Hidden
