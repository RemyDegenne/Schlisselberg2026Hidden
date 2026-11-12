/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

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

## Main definitions

* `LMLExplore.IsPowerBarrier ν c₁ c₂ r`: `r` is twice differentiable on `(0, 1)` with
  `c₁ / x ^ ν ≤ r'' x ≤ c₂ / x ^ ν` there, for `ν ≥ 1` and `c₁ > 0`.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open Set

namespace LMLExplore

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

end LMLExplore
