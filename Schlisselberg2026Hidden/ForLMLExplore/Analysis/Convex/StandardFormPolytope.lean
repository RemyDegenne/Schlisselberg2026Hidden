/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Analysis.Convex.Simplex

/-!
# Polytopes in standard form inside the simplex

For a finite type `α`, a linear map `A` from `α → ℝ` to a real vector space `M` and `b : M`, the
**polytope in standard form** is `K = {w | (∀ a, 0 ≤ w a) ∧ A w = b}`, and its points with
positive coordinates form `K⁺ = {w | (∀ a, 0 < w a) ∧ A w = b}`. Both are convex, and from a point
of `K` one can move along the difference of two points of `K` as long as the coordinates stay
nonnegative. Mirror descent with a barrier regularizer on `K` takes its steps in `K⁺`, and its
analysis on a polytope `K` contained in the simplex measures the steps with the `ℓ¹` norm: a
difference `v` of two points of the simplex has `∑ a, v a = 0`, hence `|v a| ≤ ‖v‖₁ / 2` and
`∑ a, v a ^ 2 ≤ ‖v‖₁ ^ 2 / 2` [SSKM26, Lemma 31], and `‖v‖₁ ≤ 2`.

## Main statements

* `LMLExplore.convex_setOf_forall_nonneg_and_apply_eq`,
  `LMLExplore.convex_setOf_forall_pos_and_apply_eq`: `K` and `K⁺` are convex.
* `LMLExplore.apply_add_smul_sub_eq`: moving from a point of `A ⁻¹' {b}` along the difference of
  two such points stays in `A ⁻¹' {b}`.
* `LMLExplore.abs_le_sum_abs_div_two_of_sum_eq_zero`,
  `LMLExplore.sum_sq_le_sq_sum_abs_div_two_of_sum_eq_zero`: the `ℓ¹` bounds on a vector with
  zero sum [SSKM26, Lemma 31].
* `LMLExplore.sum_abs_sub_le_two_of_mem_simplex`: the `ℓ¹` diameter of the simplex is at most `2`.
* `LMLExplore.mem_Ioo_of_mem_simplex_of_pos`: in dimension at least `2`, the coordinates of a
  point of the simplex with positive coordinates lie in `(0, 1)`.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open Finset

namespace LMLExplore

variable {α : Type*} {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- A polytope in standard form `{w | (∀ a, 0 ≤ w a) ∧ A w = b}` is convex. -/
lemma convex_setOf_forall_nonneg_and_apply_eq (A : (α → ℝ) →ₗ[ℝ] M) (b : M) :
    Convex ℝ {w : α → ℝ | (∀ a, 0 ≤ w a) ∧ A w = b} := by
  intro x hx y hy s t hs ht hst
  refine ⟨fun a ↦ ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx.1 a
    have := hy.1 a
    positivity
  · rw [map_add, map_smul, map_smul, hx.2, hy.2, ← add_smul, hst, one_smul]

/-- The points with positive coordinates of a polytope in standard form,
`{w | (∀ a, 0 < w a) ∧ A w = b}`, form a convex set. -/
lemma convex_setOf_forall_pos_and_apply_eq (A : (α → ℝ) →ₗ[ℝ] M) (b : M) :
    Convex ℝ {w : α → ℝ | (∀ a, 0 < w a) ∧ A w = b} := by
  intro x hx y hy s t hs ht hst
  refine ⟨fun a ↦ ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hxa := hx.1 a
    have hya := hy.1 a
    rcases hs.eq_or_lt with rfl | hs'
    · rw [zero_add] at hst
      rw [hst]
      linarith
    · nlinarith
  · rw [map_add, map_smul, map_smul, hx.2, hy.2, ← add_smul, hst, one_smul]

/-- Moving from a point `x` with `A x = b` along the difference of two points `y, z` with
`A y = A z = b` keeps the value `b`. -/
lemma apply_add_smul_sub_eq {A : (α → ℝ) →ₗ[ℝ] M} {b : M} {x y z : α → ℝ} (hx : A x = b)
    (hy : A y = b) (hz : A z = b) (γ : ℝ) : A (x + γ • (y - z)) = b := by
  rw [map_add, map_smul, map_sub, hx, hy, hz, sub_self, smul_zero, add_zero]

variable [Fintype α]

/-- A coordinate of a vector with zero sum is at most half its `ℓ¹` norm in absolute value
[SSKM26, Lemma 31]. -/
lemma abs_le_sum_abs_div_two_of_sum_eq_zero {v : α → ℝ} (hv : ∑ a, v a = 0) (a : α) :
    |v a| ≤ (∑ j, |v j|) / 2 := by
  classical
  have h1 : v a = -∑ j ∈ univ.erase a, v j := by
    rw [← add_sum_erase _ _ (mem_univ a)] at hv
    linarith
  have h2 : |v a| ≤ ∑ j ∈ univ.erase a, |v j| := by
    rw [h1, abs_neg]
    exact abs_sum_le_sum_abs _ _
  have h3 : ∑ j, |v j| = |v a| + ∑ j ∈ univ.erase a, |v j| :=
    (add_sum_erase _ _ (mem_univ a)).symm
  linarith

/-- The sum of the squares of the coordinates of a vector with zero sum is at most half the square
of its `ℓ¹` norm [SSKM26, Lemma 31]. -/
lemma sum_sq_le_sq_sum_abs_div_two_of_sum_eq_zero {v : α → ℝ} (hv : ∑ a, v a = 0) :
    ∑ a, v a ^ 2 ≤ (∑ a, |v a|) ^ 2 / 2 := by
  calc ∑ a, v a ^ 2 = ∑ a, |v a| * |v a| := by
        refine sum_congr rfl fun a _ ↦ ?_
        rw [abs_mul_abs_self, sq]
    _ ≤ ∑ a, (∑ j, |v j|) / 2 * |v a| :=
        sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_right
          (abs_le_sum_abs_div_two_of_sum_eq_zero hv a) (abs_nonneg _)
    _ = (∑ a, |v a|) ^ 2 / 2 := by
        rw [← mul_sum]
        ring

/-- The difference of two points of the simplex has zero sum. -/
lemma sum_sub_eq_zero_of_mem_simplex {y z : α → ℝ} (hy : y ∈ simplex α) (hz : z ∈ simplex α) :
    ∑ a, (y a - z a) = 0 := by
  rw [sum_sub_distrib, (mem_simplex_iff.mp hy).2, (mem_simplex_iff.mp hz).2, sub_self]

/-- The `ℓ¹` distance between two points of the simplex is at most `2`. -/
lemma sum_abs_sub_le_two_of_mem_simplex {y z : α → ℝ} (hy : y ∈ simplex α)
    (hz : z ∈ simplex α) : ∑ a, |y a - z a| ≤ 2 := by
  rw [mem_simplex_iff] at hy hz
  calc ∑ a, |y a - z a| ≤ ∑ a, (y a + z a) := by
        refine sum_le_sum fun a _ ↦ abs_le.mpr ⟨?_, ?_⟩ <;> linarith [hy.1 a, hz.1 a]
    _ = 2 := by rw [sum_add_distrib, hy.2, hz.2]; norm_num

/-- In dimension at least `2`, the coordinates of a point of the simplex with positive coordinates
lie in `(0, 1)`. -/
lemma mem_Ioo_of_mem_simplex_of_pos (h2 : 2 ≤ Fintype.card α) {w : α → ℝ} (hw : w ∈ simplex α)
    (hpos : ∀ a, 0 < w a) (a : α) : w a ∈ Set.Ioo 0 1 := by
  classical
  rw [mem_simplex_iff] at hw
  refine ⟨hpos a, ?_⟩
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega) a
  have h : w a + w j ≤ ∑ k, w k := by
    rw [← sum_pair hj.symm]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun k _ _ ↦ (hpos k).le
  linarith [hpos j, hw.2]

end LMLExplore
