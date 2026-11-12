/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Analysis.Convex.NegEntropy
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Lemmas 43 and 44 of [SSKM26]: the polytope of Theorem 8

The lower bound of Theorem 8 of [SSKM26] lives on a polytope `K_m` in standard form, in dimension
`d = 5 m + 2`. We index the coordinates by `Fin m × Fin 5 ⊕ Fin 2`: for `i : Fin m`, the
coordinate `.inl (i, 0)` is the paper's `X i`, the coordinates `.inl (i, k)` for `k = 1, 2, 3` are
its `Y k i`, `.inl (i, 4)` is its `Z i`, and `.inr 0`, `.inr 1` are its `P` and `Q`.

The paper defines `K_m = {w ≥ 0, A w = A u}` for an explicit matrix `A` with `4 m + 1` rows and the
uniform point `u`, and computes a basis of `ker A` (Lemma 43 of [SSKM26]). Its corrected proof
only uses the description of `K_m` by coordinates, which we take as the definition: `w ∈ K_m` iff
`w ≥ 0` and, for every `i`, `w (Y 1 i) = w (Y 2 i) = w (Y 3 i)`, `w (Z i) = w P`,
`w (X i) + 3 w (Y 1 i) + w (Z i) = 5 / d`, and `w P + w Q = 2 / d`. These are `4 m + 1` linear
equations (`polytope_eq_setOf_constraint`), so `K_m` is in standard form.

## Main definitions

* `PolytopeLower.polytope m`: the polytope `K_m`.
* `PolytopeLower.comparator m`: the comparator `w*` of Theorem 8 of [SSKM26], equal to `5 / d` on
  the `X`-coordinates, `2 / d` on `Q` and `0` elsewhere.
* `PolytopeLower.IsShapedLoss`: the loss vectors of the construction, `0` on the `X`- and
  `Q`-coordinates and `1` on the `Y`-coordinates.

## Main statements

* `PolytopeLower.polytope_subset_simplex`, `PolytopeLower.uniform_mem_polytope`,
  `PolytopeLower.comparator_mem_polytope`: [SSKM26, Lemma 44], the polytope lies in the simplex
  and contains the uniform point and the comparator.
* `PolytopeLower.bregDiv_comparator_uniform`: the Bregman divergence of the negative entropy from
  the uniform point to the comparator is `(5 m log 5 + 2 log 2) / d`.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore Finset Real

namespace Schlisselberg2026Hidden.PolytopeLower

variable {m : ℕ}

/-- The number of coordinates is `d = 5 m + 2`. -/
lemma card_coord (m : ℕ) : Fintype.card (Fin m × Fin 5 ⊕ Fin 2) = 5 * m + 2 := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

/-- A sum over the coordinates, written block by block. -/
lemma sum_coord {M : Type*} [AddCommMonoid M] (f : Fin m × Fin 5 ⊕ Fin 2 → M) :
    ∑ j, f j = ∑ i, (f (.inl (i, 0)) + f (.inl (i, 1)) + f (.inl (i, 2)) + f (.inl (i, 3)) +
      f (.inl (i, 4))) + (f (.inr 0) + f (.inr 1)) := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_five, Fin.sum_univ_two]

/-- The polytope `K_m` of Theorem 8 of [SSKM26], described by coordinates (Lemma 43 of [SSKM26]):
the nonnegative `w` with `w (Y 1 i) = w (Y 2 i) = w (Y 3 i)`, `w (Z i) = w P`,
`w (X i) + 3 w (Y 1 i) + w (Z i) = 5 / d` for every `i`, and `w P + w Q = 2 / d`. -/
def polytope (m : ℕ) : Set (Fin m × Fin 5 ⊕ Fin 2 → ℝ) :=
  {w | (∀ j, 0 ≤ w j) ∧
    (∀ i, w (.inl (i, 2)) = w (.inl (i, 1)) ∧ w (.inl (i, 3)) = w (.inl (i, 1)) ∧
      w (.inl (i, 4)) = w (.inr 0) ∧
      w (.inl (i, 0)) + 3 * w (.inl (i, 1)) + w (.inl (i, 4)) = 5 / (5 * m + 2)) ∧
    w (.inr 0) + w (.inr 1) = 2 / (5 * m + 2)}

/-- The `4 m + 1` linear constraints of `polytope m`. -/
noncomputable def constraint (m : ℕ) :
    Fin m × Fin 4 ⊕ Unit → (Fin m × Fin 5 ⊕ Fin 2 → ℝ) →ₗ[ℝ] ℝ
  | .inl (i, k) =>
    ![LinearMap.proj (.inl (i, 2)) - LinearMap.proj (.inl (i, 1)),
      LinearMap.proj (.inl (i, 3)) - LinearMap.proj (.inl (i, 1)),
      LinearMap.proj (.inl (i, 4)) - LinearMap.proj (.inr 0),
      LinearMap.proj (.inl (i, 0)) + (3 : ℝ) • LinearMap.proj (.inl (i, 1)) +
        LinearMap.proj (.inl (i, 4))] k
  | .inr _ => LinearMap.proj (.inr 0) + LinearMap.proj (.inr 1)

/-- The right-hand sides of the constraints of `polytope m`. -/
noncomputable def constraintValue (m : ℕ) : Fin m × Fin 4 ⊕ Unit → ℝ
  | .inl (_, k) => ![0, 0, 0, 5 / (5 * m + 2 : ℝ)] k
  | .inr _ => 2 / (5 * m + 2)

/-- `polytope m` is a polytope in standard form: the nonnegative solutions of `4 m + 1` linear
equations. -/
lemma polytope_eq_setOf_constraint (m : ℕ) :
    polytope m = {w | (∀ j, 0 ≤ w j) ∧ ∀ ρ, constraint m ρ w = constraintValue m ρ} := by
  ext w
  refine and_congr_right fun _ ↦ ⟨fun ⟨h, hPQ⟩ ↦ ?_, fun h ↦ ⟨fun i ↦ ?_, ?_⟩⟩
  · rintro (⟨i, k⟩ | _)
    · obtain ⟨h2, h3, h4, h5⟩ := h i
      fin_cases k <;> simp [constraint, constraintValue, h2, h3, h4, h5.symm]
    · simpa [constraint, constraintValue] using hPQ
  · have h2 : w (.inl (i, 2)) = w (.inl (i, 1)) := by
      simpa [constraint, constraintValue, sub_eq_zero] using h (.inl (i, 0))
    have h3 : w (.inl (i, 3)) = w (.inl (i, 1)) := by
      simpa [constraint, constraintValue, sub_eq_zero] using h (.inl (i, 1))
    have h4 : w (.inl (i, 4)) = w (.inr 0) := by
      simpa [constraint, constraintValue, sub_eq_zero] using h (.inl (i, 2))
    have h5 : w (.inl (i, 0)) + 3 * w (.inl (i, 1)) + w (.inl (i, 4)) = 5 / (5 * m + 2) := by
      simpa [constraint, constraintValue] using h (.inl (i, 3))
    exact ⟨h2, h3, h4, h5⟩
  · simpa [constraint, constraintValue] using h (.inr ())

/-- **The polytope lies in the simplex** [SSKM26, Lemma 44]. -/
lemma polytope_subset_simplex (m : ℕ) : polytope m ⊆ simplex (Fin m × Fin 5 ⊕ Fin 2) := by
  rintro w ⟨h0, h, hPQ⟩
  refine mem_simplex_iff.mpr ⟨h0, ?_⟩
  rw [sum_coord]
  have hi : ∀ i, w (.inl (i, 0)) + w (.inl (i, 1)) + w (.inl (i, 2)) + w (.inl (i, 3)) +
      w (.inl (i, 4)) = 5 / (5 * m + 2) := fun i ↦ by
    obtain ⟨h2, h3, -, h5⟩ := h i
    linarith
  rw [Finset.sum_congr rfl fun i _ ↦ hi i, hPQ, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **The polytope contains the uniform point** [SSKM26, Lemma 44]. -/
lemma uniform_mem_polytope (m : ℕ) :
    (fun _ ↦ (5 * m + 2 : ℝ)⁻¹) ∈ polytope m := by
  refine ⟨fun _ ↦ by positivity, fun i ↦ ⟨rfl, rfl, rfl, ?_⟩, ?_⟩ <;>
  · field_simp
    ring

/-- The comparator `w*` of Theorem 8 of [SSKM26]: `5 / d` on the `X`-coordinates, `2 / d` on `Q`,
and `0` elsewhere. -/
noncomputable def comparator (m : ℕ) : Fin m × Fin 5 ⊕ Fin 2 → ℝ :=
  Sum.elim (fun p ↦ if p.2 = 0 then 5 / (5 * m + 2 : ℝ) else 0) ![0, 2 / (5 * m + 2 : ℝ)]

@[simp] lemma comparator_inl (i : Fin m) (k : Fin 5) :
    comparator m (.inl (i, k)) = if k = 0 then 5 / (5 * m + 2 : ℝ) else 0 := rfl

@[simp] lemma comparator_inr_zero : comparator m (.inr 0) = 0 := rfl

@[simp] lemma comparator_inr_one : comparator m (.inr 1) = 2 / (5 * m + 2) := rfl

/-- **The polytope contains the comparator** [SSKM26, Lemma 44]. -/
lemma comparator_mem_polytope (m : ℕ) : comparator m ∈ polytope m := by
  refine ⟨?_, fun i ↦ ?_, ?_⟩
  · rintro (⟨i, k⟩ | k)
    · simp only [comparator_inl]
      split_ifs <;> positivity
    · fin_cases k <;> simp [show (0 : ℝ) ≤ 2 / (5 * m + 2) by positivity]
  · simp
  · simp

/-- The loss vectors of the construction of Theorem 8 of [SSKM26]: `0` on the `X`- and
`Q`-coordinates and `1` on the `Y`-coordinates; the `Z`- and `P`-coordinates are free. -/
def IsShapedLoss (x : Fin m × Fin 5 ⊕ Fin 2 → ℝ) : Prop :=
  (∀ i, x (.inl (i, 0)) = 0 ∧ x (.inl (i, 1)) = 1 ∧ x (.inl (i, 2)) = 1 ∧ x (.inl (i, 3)) = 1) ∧
    x (.inr 1) = 0

/-- The comparator has zero loss for the losses of the construction (its support is the `X`- and
`Q`-coordinates) [SSKM26, proof of Theorem 49]. -/
lemma sum_mul_comparator_eq_zero {x : Fin m × Fin 5 ⊕ Fin 2 → ℝ} (hx : IsShapedLoss x) :
    ∑ j, x j * comparator m j = 0 := by
  rw [sum_coord]
  simp [(hx.1 _).1, hx.2]

/-- A linear form on `ι → ℝ` given by its coefficients, applied to a vector. -/
lemma sum_smul_proj_apply {ι : Type*} [Fintype ι] (c v : ι → ℝ) :
    (∑ j, c j • ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ) v = ∑ j, c j * v j := by
  simp

/-- The Bregman divergence of the negative entropy from the uniform point to the comparator,
`(5 m log 5 + 2 log 2) / d`. -/
lemma bregDiv_comparator_uniform (m : ℕ) :
    bregDiv negEntropy (comparator m) (fun _ ↦ (5 * m + 2 : ℝ)⁻¹)
        (∑ j, log (5 * m + 2 : ℝ)⁻¹ • ContinuousLinearMap.proj j :
          (Fin m × Fin 5 ⊕ Fin 2 → ℝ) →L[ℝ] ℝ) =
      (5 * m * log 5 + 2 * log 2) / (5 * m + 2) := by
  have hd : (0 : ℝ) < 5 * m + 2 := by positivity
  simp only [bregDiv, negEntropy_def, sum_smul_proj_apply, Pi.sub_apply]
  rw [sum_coord, sum_coord, sum_coord]
  simp only [comparator_inl, comparator_inr_zero, comparator_inr_one, ite_true,
    Fin.reduceEq, ite_false, log_zero, mul_zero, sub_zero, zero_sub,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [log_div (by norm_num) hd.ne', log_div (by norm_num) hd.ne', log_inv]
  field_simp
  ring

/-- The Bregman divergence from the uniform point to the comparator is at most `9 m / d` when
`m ≥ 2`. -/
lemma bregDiv_comparator_uniform_le (hm : 2 ≤ m) :
    bregDiv negEntropy (comparator m) (fun _ ↦ (5 * m + 2 : ℝ)⁻¹)
        (∑ j, log (5 * m + 2 : ℝ)⁻¹ • ContinuousLinearMap.proj j :
          (Fin m × Fin 5 ⊕ Fin 2 → ℝ) →L[ℝ] ℝ) ≤
      9 * m / (5 * m + 2) := by
  rw [bregDiv_comparator_uniform]
  gcongr
  have h5 : log 5 ≤ 2 * log 2 + 1 / 4 := by
    have h := log_le_sub_one_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
    rw [show (5 : ℝ) = 2 * 2 * (5 / 4) by norm_num, log_mul (by norm_num) (by norm_num),
      log_mul (by norm_num) (by norm_num)]
    linarith
  have h2 : log 2 < 0.7 := by
    have := log_two_lt_d9
    linarith
  have h2' : 0 < log 2 := log_pos (by norm_num)
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

end Schlisselberg2026Hidden.PolytopeLower
