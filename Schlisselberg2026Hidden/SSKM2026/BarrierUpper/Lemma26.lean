/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.SSKM2026.BarrierUpper.Lemma11

/-!
# The one-round inequality of approximate mirror descent with a power barrier

Let `K = {w | w ≥ 0, A w = b}` be contained in the simplex of dimension at least `2`, `r` a power
barrier with upper constant `c₂`, and `x` an `ε`-approximate step of mirror descent on the points of
`K` with positive coordinates, from `a`, with the potential `R w = ∑ i, r (w i)` and a loss `ℓ`.
If the coordinates of `x` are at least `ψ > 0`, and `ε` is small,
`c₂ (ψ / 2)^{-ν} ε ≤ η⁴ / 4` and `4 ε ≤ η²`, then for every `u ∈ K`,
`η ⟨ℓ, x - u⟩ ≤ D_R(u, a) - D_R(u, x) - D_R(x, a) + η²`.

This is the inequality of exact mirror descent, from the first-order condition at the step and the
three-point identity [SSKM26, Lemma 26], up to `η²`. The approximate first-order condition is used
along the initial half of the segment `[x, u]`, where the coordinates stay above `ψ / 2`: the
regularizer is not smooth on the whole segment when `u` has zero coordinates
(`neg_max_le_mul_sum_of_isApproxMirrorDescentStep`). The point `u` may have zero coordinates: the
value `r (u i)` cancels in `D_R(u, a) - D_R(u, x)`.

## Main statements

* `Schlisselberg2026Hidden.mul_sum_mul_sub_le_of_isApproxMirrorDescentStep`: the one-round
  inequality, with [SSKM26, Lemma 26].

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α] {M : Type*} [AddCommGroup M] [Module ℝ M]
  {ν c₁ c₂ : ℝ} {r : ℝ → ℝ} {A : (α → ℝ) →ₗ[ℝ] M} {b : M} {η ε : ℝ} {ℓ a x : α → ℝ}

/-- **The one-round inequality** of approximate mirror descent with a power barrier on a
polytope, with the three-point identity [SSKM26, Lemma 26]. Let `K = {w | w ≥ 0, A w = b}` be
contained in the simplex of dimension at least `2`, `r` a power barrier, and `x` an
`ε`-approximate step of mirror descent on the points of `K` with positive coordinates, from `a`,
with the potential `R w = ∑ i, r (w i)` and a loss `ℓ`. If the coordinates of `x` are at least
`ψ > 0`, `c₂ / (ψ / 2)^ν ε ≤ η⁴ / 4` and `4 ε ≤ η²`, then for every `u ∈ K`,
`η ⟨ℓ, x - u⟩ ≤ D_R(u, a) - D_R(u, x) - D_R(x, a) + η²`. No bound on the loss is needed. -/
lemma mul_sum_mul_sub_le_of_isApproxMirrorDescentStep (h2 : 2 ≤ Fintype.card α)
    (hr : IsPowerBarrier ν c₁ c₂ r) (hK : {w | (∀ i, 0 ≤ w i) ∧ A w = b} ⊆ simplex α)
    (h : IsApproxMirrorDescentStep {w | (∀ i, 0 < w i) ∧ A w = b} (fun w ↦ ∑ i, r (w i)) η
      (∑ i, ℓ i • ContinuousLinearMap.proj i) a
      (∑ i, deriv r (a i) • ContinuousLinearMap.proj i) ε x)
    {ψ : ℝ} (hψ : 0 < ψ) (hx : ∀ i, ψ ≤ x i) (hE3 : c₂ / (ψ / 2) ^ ν * ε ≤ η ^ 4 / 4)
    (hE4 : 4 * ε ≤ η ^ 2) {u : α → ℝ} (hu : u ∈ {w : α → ℝ | (∀ i, 0 ≤ w i) ∧ A w = b}) :
    η * ∑ i, ℓ i * (x i - u i) ≤
      bregDiv (fun w : α → ℝ ↦ ∑ i, r (w i)) u a
          (∑ i, deriv r (a i) • ContinuousLinearMap.proj i : (α → ℝ) →L[ℝ] ℝ) -
        bregDiv (fun w : α → ℝ ↦ ∑ i, r (w i)) u x
          (∑ i, deriv r (x i) • ContinuousLinearMap.proj i : (α → ℝ) →L[ℝ] ℝ) -
        bregDiv (fun w : α → ℝ ↦ ∑ i, r (w i)) x a
          (∑ i, deriv r (a i) • ContinuousLinearMap.proj i : (α → ℝ) →L[ℝ] ℝ) + η ^ 2 := by
  set M' := c₂ / (ψ / 2) ^ ν with hM'
  have hε := h.nonneg
  have hxK := h.mem
  have hxI := mem_Ioo_of_mem_polytope h2 hK hxK
  have hM'0 : 0 ≤ M' := by have := hr.upper_pos; positivity
  have hxK' : x ∈ {w : α → ℝ | (∀ i, 0 ≤ w i) ∧ A w = b} := ⟨fun j ↦ (hxK.1 j).le, hxK.2⟩
  set d : α → ℝ := u - x with hd
  have hdi (i : α) : d i = u i - x i := rfl
  have hdsum : ∑ i, d i = 0 := sum_sub_eq_zero_of_mem_simplex (hK hu) (hK hxK')
  have hdabs : ∑ i, |d i| ≤ 2 := sum_abs_sub_le_two_of_mem_simplex (hK hu) (hK hxK')
  have hdsq : ∑ i, d i ^ 2 ≤ 2 := by
    have h1 := sum_sq_le_sq_sum_abs_div_two_of_sum_eq_zero hdsum
    have h2 : (∑ i, |d i|) ^ 2 ≤ 2 ^ 2 :=
      pow_le_pow_left₀ (sum_nonneg fun i _ ↦ abs_nonneg _) hdabs 2
    linarith
  -- along `[x, x + (u - x) / 2]` the coordinates stay above `ψ / 2`
  have hlow : ∀ γ ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ i, ψ / 2 ≤ x i + γ * d i := by
    intro γ hγ i
    have h1 : x i + γ * d i = (1 - γ) * x i + γ * u i := by rw [hdi]; ring
    have h2 : 0 ≤ γ * u i := mul_nonneg hγ.1 (hu.1 i)
    have h3 : ψ / 2 ≤ (1 - γ) * x i := by nlinarith [hγ.2, hx i]
    linarith
  have hS : ∀ γ ∈ Set.Icc (0 : ℝ) (1 / 2),
      x + γ • d ∈ {w : α → ℝ | (∀ i, 0 < w i) ∧ A w = b} := by
    intro γ hγ
    refine ⟨fun i ↦ ?_, apply_add_smul_sub_eq hxK.2 hu.2 hxK.2 γ⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hlow γ hγ i]
  have hQ : ∀ γ ∈ Set.Icc (0 : ℝ) (1 / 2),
      ∑ i, (r (x i + γ * d i) - r (x i) - deriv r (x i) * (γ * d i)) ≤ 2 * M' / 2 * γ ^ 2 := by
    intro γ hγ
    have hI : ∀ i, x i + γ * d i ∈ Set.Ioo 0 1 := fun i ↦ by
      simpa using mem_Ioo_of_mem_polytope h2 hK (hS γ hγ) i
    calc ∑ i, (r (x i + γ * d i) - r (x i) - deriv r (x i) * (γ * d i))
        ≤ ∑ i, M' * (γ * d i) ^ 2 / 2 := sum_le_sum fun i _ ↦ by
          have h1 := hr.sub_sub_le_mul_sq (M := M') (hI i) (hxI i) fun s hs ↦
            hr.deriv_deriv_le_div_rpow (Set.ordConnected_Ioo.uIcc_subset (hI i) (hxI i) hs)
              (half_pos hψ) ((le_min (hlow γ hγ i) (by linarith [hx i])).trans hs.1)
          simpa only [add_sub_cancel_left] using h1
      _ = M' / 2 * γ ^ 2 * ∑ i, d i ^ 2 := by
          rw [mul_sum]
          exact sum_congr rfl fun i _ ↦ by ring
      _ ≤ M' / 2 * γ ^ 2 * 2 := mul_le_mul_of_nonneg_left hdsq (by positivity)
      _ = 2 * M' / 2 * γ ^ 2 := by ring
  have h6 := neg_max_le_mul_sum_of_isApproxMirrorDescentStep h (by norm_num) hS hQ
  -- the error of the first-order condition is at most `η² / 2`
  have hsq : √(2 * (2 * M') * ε) ≤ η ^ 2 := by
    rw [show 2 * (2 * M') * ε = 4 * (M' * ε) by ring]
    calc √(4 * (M' * ε)) ≤ √((η ^ 2) ^ 2) := sqrt_le_sqrt (by nlinarith)
      _ = η ^ 2 := sqrt_sq (sq_nonneg η)
  have hmax : max (1 / 2 * √(2 * (2 * M') * ε)) (2 * ε) ≤ η ^ 2 / 2 :=
    max_le (by linarith) (by linarith)
  set G := ∑ i, (η * ℓ i + deriv r (x i) - deriv r (a i)) * d i with hG
  have hG1 : -η ^ 2 ≤ G := by linarith
  -- the three-point identity
  have hid : η * ∑ i, ℓ i * (x i - u i) + G =
      bregDiv (fun w : α → ℝ ↦ ∑ i, r (w i)) u a
          (∑ i, deriv r (a i) • ContinuousLinearMap.proj i : (α → ℝ) →L[ℝ] ℝ) -
        bregDiv (fun w : α → ℝ ↦ ∑ i, r (w i)) u x
          (∑ i, deriv r (x i) • ContinuousLinearMap.proj i : (α → ℝ) →L[ℝ] ℝ) -
        bregDiv (fun w : α → ℝ ↦ ∑ i, r (w i)) x a
          (∑ i, deriv r (a i) • ContinuousLinearMap.proj i : (α → ℝ) →L[ℝ] ℝ) := by
    rw [bregDiv_sum_apply, bregDiv_sum_apply, bregDiv_sum_apply, hG, mul_sum, ← sum_add_distrib,
      ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [hdi]
    ring
  linarith

end Schlisselberg2026Hidden
