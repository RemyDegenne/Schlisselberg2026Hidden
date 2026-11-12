/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.Analysis.Convex.NegEntropy
public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent
public import Schlisselberg2026Hidden.SSKM2026.EntropyUpper.Lemma21
public import LMLExplore.Analysis.Convex.NegEntropy

/-!
# Lemmas 22 and 26 of [SSKM26] for the negative entropy: one approximate step

On the simplex, with the negative entropy `negEntropy` and its derivative
`∑ i, log (w i) • proj i` at a point `w` with positive coordinates, let `w'` be an `ε`-approximate
mirror descent step from `w` for the loss `ℓ` with learning rate `η`, with positive coordinates
too, and let `g i = η ℓ i + log (w' i) - log (w i)` be the gradient at `w'` of the objective
`φ x = η ⟨ℓ, x⟩ + D(x, w)` of the step. The three-point identity [SSKM26, Lemma 26] gives
`φ x - φ w' = ⟨g, x - w'⟩ + D(x, w')`, so the step condition says that
`⟨g, x - w'⟩ + D(x, w') ≥ -ε` for every `x` of the simplex.

With the `χ²` bound on `D(·, w')` (Lemma 21 of [SSKM26]), moving from `w'` a fraction `u` of the
way towards `w' + h` gives the approximate first-order condition in the direction `h`:
`⟨g, h⟩ ≥ -ε / u - u ∑ i, h i ^ 2 / w' i` [SSKM26, Lemma 22]. The paper optimizes `u`, which
gives `⟨g, h⟩ ≥ -2 max (√(ε Q), ε)` with `Q = ∑ i, h i ^ 2 / w' i`; the analysis of the negative
entropy always chooses `u` explicitly.

## Main statements

* `Schlisselberg2026Hidden.neg_le_of_isApproxMirrorDescentStep_negEntropy`:
  [SSKM26, Lemma 26], the step condition in three-point form.
* `Schlisselberg2026Hidden.neg_div_sub_le_of_isApproxMirrorDescentStep_negEntropy`:
  [SSKM26, Lemma 22], for the negative entropy.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α]

/-- The linear map `∑ i, ℓ i • proj i` is `x ↦ ∑ i, ℓ i * x i`. -/
lemma sum_smul_proj_apply (ℓ x : α → ℝ) :
    (∑ i, ℓ i • ContinuousLinearMap.proj i : (α → ℝ) →L[ℝ] ℝ) x = ∑ i, ℓ i * x i := by
  simp

variable {η ε : ℝ} {ℓ w w' : α → ℝ}

/-- **The step condition in three-point form** [SSKM26, Lemma 26]. If `w'` is an
`ε`-approximate step of mirror descent on the simplex with the negative entropy from `w`, both
with positive coordinates, then with `g i = η ℓ i + log (w' i) - log (w i)`, for every `x` of the
simplex, `-ε ≤ ⟨g, x - w'⟩ + D(x, w')`. -/
lemma neg_le_of_isApproxMirrorDescentStep_negEntropy (hw : ∀ i, 0 < w i) (hw' : ∀ i, 0 < w' i)
    (h : IsApproxMirrorDescentStep (simplex α) negEntropy η
      (∑ i, ℓ i • ContinuousLinearMap.proj i) w (∑ i, log (w i) • ContinuousLinearMap.proj i) ε w')
    {x : α → ℝ} (hx : x ∈ simplex α) :
    -ε ≤ ∑ i, (η * ℓ i + log (w' i) - log (w i)) * (x i - w' i) +
      ∑ i, (x i * log (x i / w' i) - x i + w' i) := by
  have h_le := h.le_add x hx
  rw [bregDiv_negEntropy_pi_eq fun i h ↦ absurd h (hw i).ne',
    bregDiv_negEntropy_pi_eq fun i h ↦ absurd h (hw i).ne', sum_smul_proj_apply,
    sum_smul_proj_apply, mul_sum, mul_sum] at h_le
  have h_eq : ∑ i, (η * ℓ i + log (w' i) - log (w i)) * (x i - w' i) +
      ∑ i, (x i * log (x i / w' i) - x i + w' i) =
      (∑ i, η * (ℓ i * x i) + ∑ i, (x i * log (x i / w i) - x i + w i)) -
        (∑ i, η * (ℓ i * w' i) + ∑ i, (w' i * log (w' i / w i) - w' i + w i)) := by
    simp only [← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [mul_log_div_eq_sub _ (hw i).ne', mul_log_div_eq_sub _ (hw i).ne',
      mul_log_div_eq_sub _ (hw' i).ne']
    ring
  rw [h_eq]
  linarith

/-- **The approximate first-order condition** [SSKM26, Lemma 22], for the negative entropy on the
simplex. If `w'` is an `ε`-approximate step from `w`, both with positive coordinates, `w' + h`
lies in the simplex and `0 < u ≤ 1`, then with `g i = η ℓ i + log (w' i) - log (w i)`,
`-ε / u - u ∑ i, h i ^ 2 / w' i ≤ ⟨g, h⟩`. -/
lemma neg_div_sub_le_of_isApproxMirrorDescentStep_negEntropy (hw : ∀ i, 0 < w i)
    (hw' : ∀ i, 0 < w' i)
    (h : IsApproxMirrorDescentStep (simplex α) negEntropy η
      (∑ i, ℓ i • ContinuousLinearMap.proj i) w (∑ i, log (w i) • ContinuousLinearMap.proj i) ε w')
    {v : α → ℝ} (hv : w' + v ∈ simplex α) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    -ε / u - u * ∑ i, v i ^ 2 / w' i ≤ ∑ i, (η * ℓ i + log (w' i) - log (w i)) * v i := by
  -- the point `w' + u v` is a convex combination of `w'` and `w' + v`
  have hx : w' + u • v ∈ simplex α := by
    have := convex_simplex α h.mem hv (sub_nonneg.2 hu1) hu.le (by ring)
    convert this using 1
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h_le := neg_le_of_isApproxMirrorDescentStep_negEntropy hw hw' h hx
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left] at h_le
  -- the `χ²` bound on `D(w' + u v, w')`
  have h_chi : ∑ i, ((w' i + u * v i) * log ((w' i + u * v i) / w' i) - (w' i + u * v i) + w' i)
      ≤ u ^ 2 * ∑ i, v i ^ 2 / w' i := by
    rw [mul_sum]
    refine sum_le_sum fun i _ ↦ ?_
    have h0 : 0 ≤ w' i + u * v i := by simpa using (mem_simplex_iff.1 hx).1 i
    calc _ ≤ (w' i + u * v i - w' i) ^ 2 / w' i := mul_log_div_sub_add_le_sq_div h0 (hw' i)
      _ = u ^ 2 * (v i ^ 2 / w' i) := by ring
  have h_lin : ∑ i, (η * ℓ i + log (w' i) - log (w i)) * (u * v i) =
      u * ∑ i, (η * ℓ i + log (w' i) - log (w i)) * v i := by
    rw [mul_sum]
    exact sum_congr rfl fun i _ ↦ by ring
  rw [h_lin] at h_le
  rw [sub_le_iff_le_add, div_le_iff₀ hu]
  nlinarith

end Schlisselberg2026Hidden
