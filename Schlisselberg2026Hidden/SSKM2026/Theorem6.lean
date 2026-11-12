/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent
public import Schlisselberg2026Hidden.ForLMLExplore.Analysis.Convex.PowerBarrier
public import LMLExplore.Analysis.Convex.Simplex

/-!
# Theorem 6 of [SSKM26]: polynomially small errors suffice for power barriers with `ν > 1`

Let `K = {w ≥ 0, A w = b}` be a polytope contained in the simplex and containing the uniform
point, and let `R w = ∑ i, r (w i)` for a power barrier `r` with exponent `ν > 1` and constants
`c₁, c₂` (Tsallis entropies, the log barrier). With
`Ψ = (2d)^{ν-1} + 8 (ν - 1) η T d / c₁`, losses in `[-1, 1]^d` and
`ε ≤ η⁴ Ψ^{-ν/(ν-1)} / (4^{ν+2} max (1, c₂))`, a polynomially small threshold, every
`ε`-approximate trajectory of mirror descent on `K` started at the uniform point has regret at most
`D_R(u, w₁) / η + (1 + 1/c₁) η T`.

The proof shows that the iterates stay at least `ψ = Ψ^{-1/(ν-1)}` away from the boundary: the
balance of the trajectory grows at most linearly in `T`, and for `ν > 1` the gradient of the
barrier only grows polynomially near `0`. A step can only halve a coordinate, which is proved by
comparing it with a point of the segment towards the initial point, inside `K`.

The paper states the theorem with `η ≤ 1/(16 c₁)`, the threshold
`η⁴ min (1/c₂, c₂) (16 η T d / c₁ + 2 (2d)^{ν-1})^{-ν/(ν-1)}`, `O(η T)` and every `w ∈ K`; its
proof applies a step-size lemma proved only on the simplex, misses a factor `1/(ν-1)` in the
lower bound on the iterates, and uses `1`-strong convexity where the barrier is only
`c₁/2`-strongly convex (`notes/paper-errata.md`).

The steps are taken on the points of `K` with positive coordinates, the domain of the barrier: in
Lean the value `r 0` is a junk value, which for the log barrier would make every positive step
fail to be approximate on `K` itself. For the same reason the comparator `u` is required to have
positive coordinates, or `r` to be right-continuous at `0` (for the log barrier, the paper's bound
is `+∞` at the boundary).

## Main statements

* `Schlisselberg2026Hidden.approxMirrorDescent_regret_le_of_isPowerBarrier`:
  [SSKM26, Theorem 6], corrected.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α] {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- **Polynomially small errors suffice for power barriers** [SSKM26, Theorem 6], with corrected
constants. Let `r` be a power barrier with exponent `ν > 1` and constants `c₁, c₂`, and let
`K = {w | w ≥ 0, A w = b}` be contained in the simplex and contain the uniform point. Let `η > 0`,
let the losses have coordinates in `[-1, 1]`, and let
`ε ≤ η⁴ Ψ^{-ν/(ν-1)} / (4^{ν+2} max (1, c₂))` with `Ψ = (2d)^{ν-1} + 8 (ν - 1) η T d / c₁` and
`d` the number of coordinates. Then every `ε`-approximate trajectory `a` of mirror descent on `K`
with potential `w ↦ ∑ i, r (w i)` and learning rate `η`, taken on the points of `K` with positive
coordinates and started at the uniform point, has regret at most
`D_R(u, a 0) / η + (1 + 1/c₁) η T` against every `u ∈ K` with positive coordinates, and against
every `u ∈ K` if `r` is right-continuous at `0`. -/
theorem approxMirrorDescent_regret_le_of_isPowerBarrier {ν c₁ c₂ : ℝ} {r : ℝ → ℝ}
    (hr : IsPowerBarrier ν c₁ c₂ r) (hν : 1 < ν) (A : (α → ℝ) →ₗ[ℝ] M) (b : M)
    (hK : {w | (∀ i, 0 ≤ w i) ∧ A w = b} ⊆ simplex α)
    (hunif : (fun _ ↦ (Fintype.card α : ℝ)⁻¹) ∈ {w : α → ℝ | (∀ i, 0 ≤ w i) ∧ A w = b})
    {η ε : ℝ} (hη : 0 < η) {T : ℕ} (ℓ : ℕ → α → ℝ) (hℓ : ∀ t < T, ∀ i, |ℓ t i| ≤ 1)
    (hε : ε ≤ η ^ 4 * ((2 * Fintype.card α) ^ (ν - 1) +
      8 * (ν - 1) * η * T * Fintype.card α / c₁) ^ (-(ν / (ν - 1))) / (4 ^ (ν + 2) * max 1 c₂))
    (a : ℕ → α → ℝ) (ha0 : a 0 = fun _ ↦ (Fintype.card α : ℝ)⁻¹)
    (ha : ∀ t < T, IsApproxMirrorDescentStep {w | (∀ i, 0 < w i) ∧ A w = b}
      (fun w ↦ ∑ i, r (w i)) η (∑ i, ℓ t i • ContinuousLinearMap.proj i) (a t)
      (∑ i, deriv r (a t i) • ContinuousLinearMap.proj i) ε (a (t + 1)))
    {u : α → ℝ} (hu : u ∈ {w : α → ℝ | (∀ i, 0 ≤ w i) ∧ A w = b})
    (hu' : (∀ i, 0 < u i) ∨ ContinuousWithinAt r (Set.Ici 0) 0) :
    regret (fun t w ↦ ∑ i, ℓ t i * w i) a u T ≤
      bregDiv (fun w ↦ ∑ i, r (w i)) u (a 0)
          (∑ i, deriv r (a 0 i) • ContinuousLinearMap.proj i : (α → ℝ) →L[ℝ] ℝ) / η +
        (1 + 1 / c₁) * η * T := by
  sorry

end Schlisselberg2026Hidden
