/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent
public import Schlisselberg2026Hidden.ForLMLExplore.Analysis.Convex.ApproxMinimizer
public import Schlisselberg2026Hidden.ForLMLExplore.Analysis.Convex.PowerBarrier

/-!
# Lemma 22 of [SSKM26], localized, for coordinate-separable regularizers

Mirror descent on a set `S ⊆ α → ℝ` with the coordinate-separable potential
`R w = ∑ i, r (w i)`, the linear loss `⟨ℓ, w⟩ = ∑ i, ℓ i * w i` and the derivative
`∑ i, r' (w i) • proj i` of `R`. The objective of a step from `a` is
`Φ(w) = η ⟨ℓ, w⟩ + D_R(w, a)`, whose formal gradient at `x` is `η ℓ + ∇R(x) - ∇R(a)`.

At an `ε`-approximate step `x`, the derivative of `Φ` at `x` in a direction `h` is not much below
`0`, provided `x + γ h` stays in `S` and `R` is smooth along `[x, x + γ₀ h]`. Only this initial
part of the segment needs a smoothness bound, while [SSKM26, Lemma 22] asks it on the whole segment
to the comparator, where a barrier is not smooth (`notes/paper-errata.md`). The proof applies the
approximate first-order condition of `LMLExplore.neg_max_le_apply_sub_of_le_add` to the restriction
of `Φ` to the line through `x` in the direction `h`.

## Main statements

* `Schlisselberg2026Hidden.sum_le_of_isApproxMirrorDescentStep`: the condition of an approximate
  step, in coordinates.
* `Schlisselberg2026Hidden.neg_max_le_mul_sum_of_isApproxMirrorDescentStep`: [SSKM26, Lemma 22],
  localized to the initial part of a segment.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α] {S : Set (α → ℝ)} {r : ℝ → ℝ} {η ε : ℝ} {ℓ a x : α → ℝ}

/-- The condition of an `ε`-approximate step `x` of mirror descent from `a` with the potential
`w ↦ ∑ i, r (w i)` and the loss `ℓ`, in coordinates: for every `y ∈ S`,
`η ⟨ℓ, x⟩ + D_R(x, a) ≤ η ⟨ℓ, y⟩ + D_R(y, a) + ε`. -/
lemma sum_le_of_isApproxMirrorDescentStep
    (h : IsApproxMirrorDescentStep S (fun w ↦ ∑ i, r (w i)) η
      (∑ i, ℓ i • ContinuousLinearMap.proj i) a
      (∑ i, deriv r (a i) • ContinuousLinearMap.proj i) ε x) {y : α → ℝ} (hy : y ∈ S) :
    η * ∑ i, ℓ i * x i + ∑ i, (r (x i) - r (a i) - deriv r (a i) * (x i - a i)) ≤
      η * ∑ i, ℓ i * y i + ∑ i, (r (y i) - r (a i) - deriv r (a i) * (y i - a i)) + ε := by
  have h1 := h.le_add y hy
  rw [bregDiv_sum_apply, bregDiv_sum_apply] at h1
  simpa only [sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul] using h1

/-- **The approximate first-order condition, localized** [SSKM26, Lemma 22]. Let `x` be an
`ε`-approximate step of mirror descent on `S` from `a`, with the potential `w ↦ ∑ i, r (w i)` and
the loss `ℓ`. Let `h` be a direction and `γ₀ ≥ 0` such that, for `γ ∈ [0, γ₀]`, `x + γ h ∈ S` and
`∑ i, D_r(x i + γ h i, x i) ≤ Q / 2 * γ ^ 2`. Then the derivative of the objective at `x` in the
direction `γ₀ h` is at least `-max (γ₀ √(2 Q ε)) (2 ε)`.

[SSKM26] asks the smoothness bound on the whole segment to the comparator; only its initial part
`[x, x + γ₀ h]` is needed. -/
lemma neg_max_le_mul_sum_of_isApproxMirrorDescentStep
    (h : IsApproxMirrorDescentStep S (fun w ↦ ∑ i, r (w i)) η
      (∑ i, ℓ i • ContinuousLinearMap.proj i) a
      (∑ i, deriv r (a i) • ContinuousLinearMap.proj i) ε x)
    {d : α → ℝ} {γ₀ Q : ℝ} (hγ₀ : 0 ≤ γ₀) (hS : ∀ γ ∈ Set.Icc 0 γ₀, x + γ • d ∈ S)
    (hQ : ∀ γ ∈ Set.Icc 0 γ₀,
      ∑ i, (r (x i + γ * d i) - r (x i) - deriv r (x i) * (γ * d i)) ≤ Q / 2 * γ ^ 2) :
    -max (γ₀ * √(2 * Q * ε)) (2 * ε) ≤
      γ₀ * ∑ i, (η * ℓ i + deriv r (x i) - deriv r (a i)) * d i := by
  set G := ∑ i, (η * ℓ i + deriv r (x i) - deriv r (a i)) * d i with hG
  -- the objective along the line through `x` in the direction `d`
  set f : ℝ → ℝ := fun s ↦ ∑ i, (η * ℓ i * (x i + s * d i) +
    (r (x i + s * d i) - r (a i) - deriv r (a i) * (x i + s * d i - a i))) with hf
  set f' : ℝ →L[ℝ] ℝ := G • ContinuousLinearMap.id ℝ ℝ with hf'
  have hf'_apply (s : ℝ) : f' s = G * s := by simp [hf']
  have hmin : ∀ z ∈ segment ℝ 0 γ₀, f 0 ≤ f z + ε := by
    intro z hz
    rw [segment_eq_Icc hγ₀] at hz
    have h1 := sum_le_of_isApproxMirrorDescentStep h (hS z hz)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
    simp only [hf, zero_mul, add_zero]
    rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib] at h1
    simpa only [mul_assoc] using h1
  have hquad : ∀ z ∈ segment ℝ 0 γ₀, bregDiv f z 0 f' ≤ Q / 2 * ‖z - 0‖ ^ 2 := by
    intro z hz
    rw [segment_eq_Icc hγ₀] at hz
    have h1 : bregDiv f z 0 f' =
        ∑ i, (r (x i + z * d i) - r (x i) - deriv r (x i) * (z * d i)) := by
      simp only [bregDiv, hf'_apply, hf, hG, sub_zero, zero_mul, add_zero, sum_mul,
        ← sum_sub_distrib]
      refine sum_congr rfl fun i _ ↦ ?_
      ring
    rw [h1, sub_zero, Real.norm_eq_abs, sq_abs]
    exact hQ z hz
  have h1 := neg_max_le_apply_sub_of_le_add hmin hquad
  rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hγ₀, hf'_apply] at h1
  linarith [mul_comm γ₀ (√(2 * Q * ε)), mul_comm γ₀ G]

end Schlisselberg2026Hidden
