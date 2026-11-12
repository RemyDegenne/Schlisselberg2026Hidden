/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.SSKM2026.BarrierUpper.Lemma22
public import Schlisselberg2026Hidden.ForLMLExplore.Analysis.Convex.StandardFormPolytope

/-!
# Lemma 11 of [SSKM26], corrected: the balance of one approximate step

Let `K = {w | w ≥ 0, A w = b}` be a polytope contained in the simplex of dimension at least `2`,
`K⁺` its points with positive coordinates, and `r` a power barrier with upper constant `c₂`. An
`ε`-approximate step `x` of mirror descent on `K⁺` from `a`, with the potential
`R w = ∑ i, r (w i)` and the loss `ℓ`, nearly satisfies the first-order condition of the exact
step along every difference `y - z` of points of `K`: if the coordinates of `x` are at least
`ψ' > 0`, then
`⟨∇R(a) - ∇R(x), y - z⟩ ≤ η ⟨ℓ, y - z⟩ + (√(c₂ (ψ' / 2)^{-ν} ε) + 2 ε / ψ') ‖y - z‖₁`.

The proof compares `x` with the points `x + γ (y - z) / ‖y - z‖₁` for `γ ≤ ψ'`, whose coordinates
stay above `ψ' / 2`, so that `r'' ≤ c₂ (ψ' / 2)^{-ν}` along the way. [SSKM26, Lemma 11] states the
exact identity for exact steps, and its proof applies Lemma 22 on a segment where the barrier is not
smooth (`notes/paper-errata.md`).

## Main statements

* `Schlisselberg2026Hidden.sum_deriv_sub_mul_le_of_isApproxMirrorDescentStep`: [SSKM26, Lemma 11],
  corrected.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α] {M : Type*} [AddCommGroup M] [Module ℝ M]
  {ν c₁ c₂ : ℝ} {r : ℝ → ℝ} {A : (α → ℝ) →ₗ[ℝ] M} {b : M} {η ε : ℝ} {ℓ a x : α → ℝ}

/-- `⟨ℓ, v⟩ ≤ ‖v‖₁` for a loss with coordinates in `[-1, 1]`. -/
lemma sum_mul_le_sum_abs (hℓ : ∀ i, |ℓ i| ≤ 1) (v : α → ℝ) : ∑ i, ℓ i * v i ≤ ∑ i, |v i| :=
  sum_le_sum fun i _ ↦ (le_abs_self _).trans <| by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hℓ i)

/-- The coordinates of a point with positive coordinates of a polytope contained in the simplex of
dimension at least `2` lie in `(0, 1)`. -/
lemma mem_Ioo_of_mem_polytope (h2 : 2 ≤ Fintype.card α)
    (hK : {w | (∀ i, 0 ≤ w i) ∧ A w = b} ⊆ simplex α) {w : α → ℝ}
    (hw : w ∈ {w : α → ℝ | (∀ i, 0 < w i) ∧ A w = b}) (i : α) : w i ∈ Set.Ioo 0 1 :=
  mem_Ioo_of_mem_simplex_of_pos h2 (hK ⟨fun j ↦ (hw.1 j).le, hw.2⟩) hw.1 i

/-- **The balance of one approximate step** [SSKM26, Lemma 11], corrected and localized. Let
`K = {w | w ≥ 0, A w = b}` be contained in the simplex of dimension at least `2`, `r` a power
barrier and `x` an `ε`-approximate step of mirror descent on the points of `K` with positive
coordinates, from `a`, with the potential `w ↦ ∑ i, r (w i)` and the loss `ℓ`. If the
coordinates of `x` are at least `ψ' > 0`, then for all `y, z ∈ K`,
`⟨∇R(a) - ∇R(x), y - z⟩ ≤ η ⟨ℓ, y - z⟩ + (√(c₂ / (ψ' / 2)^ν ε) + 2 ε / ψ') ‖y - z‖₁`. -/
lemma sum_deriv_sub_mul_le_of_isApproxMirrorDescentStep (h2 : 2 ≤ Fintype.card α)
    (hr : IsPowerBarrier ν c₁ c₂ r) (hK : {w | (∀ i, 0 ≤ w i) ∧ A w = b} ⊆ simplex α)
    (h : IsApproxMirrorDescentStep {w | (∀ i, 0 < w i) ∧ A w = b} (fun w ↦ ∑ i, r (w i)) η
      (∑ i, ℓ i • ContinuousLinearMap.proj i) a
      (∑ i, deriv r (a i) • ContinuousLinearMap.proj i) ε x)
    {ψ' : ℝ} (hψ' : 0 < ψ') (hx : ∀ i, ψ' ≤ x i) {y z : α → ℝ}
    (hy : y ∈ {w : α → ℝ | (∀ i, 0 ≤ w i) ∧ A w = b})
    (hz : z ∈ {w : α → ℝ | (∀ i, 0 ≤ w i) ∧ A w = b}) :
    ∑ i, (deriv r (a i) - deriv r (x i)) * (y i - z i) ≤
      η * ∑ i, ℓ i * (y i - z i) +
        (√(c₂ / (ψ' / 2) ^ ν * ε) + 2 * ε / ψ') * ∑ i, |y i - z i| := by
  set N := ∑ i, |y i - z i| with hN
  set M' := c₂ / (ψ' / 2) ^ ν with hM'
  set Gv := ∑ i, (η * ℓ i + deriv r (x i) - deriv r (a i)) * (y i - z i) with hGv
  have hε := h.nonneg
  have hxK := h.mem
  have hM'0 : 0 ≤ M' := by have := hr.upper_pos; positivity
  have hsum : ∑ i, (y i - z i) = 0 := sum_sub_eq_zero_of_mem_simplex (hK hy) (hK hz)
  have hN0 : 0 ≤ N := sum_nonneg fun i _ ↦ abs_nonneg _
  have hG : ∑ i, (deriv r (a i) - deriv r (x i)) * (y i - z i) =
      η * ∑ i, ℓ i * (y i - z i) - Gv := by
    rw [hGv, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    ring
  rcases hN0.eq_or_lt with hN0 | hNpos
  · have hv : ∀ i, y i - z i = 0 := fun i ↦ abs_eq_zero.mp
      ((sum_eq_zero_iff_of_nonneg fun j _ ↦ abs_nonneg _).mp hN0.symm i (mem_univ i))
    simp [hv, ← hN0]
  -- the direction `d = (y - z) / ‖y - z‖₁`
  set d : α → ℝ := fun i ↦ (y i - z i) / N with hd
  have hdsum : ∑ i, d i = 0 := by simp only [hd, ← sum_div, hsum, zero_div]
  have hdabs : ∑ i, |d i| = 1 := by
    simp only [hd, abs_div, abs_of_pos hNpos, ← sum_div]
    exact div_self hNpos.ne'
  have hdi : ∀ i, |d i| ≤ 1 / 2 := fun i ↦ by
    have := abs_le_sum_abs_div_two_of_sum_eq_zero hdsum i
    rwa [hdabs] at this
  have hdsq : ∑ i, d i ^ 2 ≤ 1 / 2 := by
    have := sum_sq_le_sq_sum_abs_div_two_of_sum_eq_zero hdsum
    rwa [hdabs, one_pow] at this
  -- along `[x, x + ψ' d]` the coordinates stay above `ψ' / 2`
  have hlow : ∀ γ ∈ Set.Icc 0 ψ', ∀ i, ψ' / 2 ≤ x i + γ * d i := by
    intro γ hγ i
    have h1 : |γ * d i| ≤ ψ' / 2 := by
      rw [abs_mul, abs_of_nonneg hγ.1]
      calc γ * |d i| ≤ ψ' * (1 / 2) := mul_le_mul hγ.2 (hdi i) (abs_nonneg _) hψ'.le
        _ = ψ' / 2 := by ring
    linarith [neg_abs_le (γ * d i), hx i]
  have hS : ∀ γ ∈ Set.Icc 0 ψ', x + γ • d ∈ {w : α → ℝ | (∀ i, 0 < w i) ∧ A w = b} := by
    intro γ hγ
    refine ⟨fun i ↦ ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith [hlow γ hγ i]
    · have h1 : γ • d = (γ / N) • (y - z) := by
        ext i
        simp only [hd, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
        ring
      rw [h1]
      exact apply_add_smul_sub_eq hxK.2 hy.2 hz.2 _
  have hxI := mem_Ioo_of_mem_polytope h2 hK hxK
  have hQ : ∀ γ ∈ Set.Icc 0 ψ',
      ∑ i, (r (x i + γ * d i) - r (x i) - deriv r (x i) * (γ * d i)) ≤ M' / 2 / 2 * γ ^ 2 := by
    intro γ hγ
    have hI : ∀ i, x i + γ * d i ∈ Set.Ioo 0 1 := fun i ↦ by
      simpa using mem_Ioo_of_mem_polytope h2 hK (hS γ hγ) i
    calc ∑ i, (r (x i + γ * d i) - r (x i) - deriv r (x i) * (γ * d i))
        ≤ ∑ i, M' * (γ * d i) ^ 2 / 2 := sum_le_sum fun i _ ↦ by
          have h1 := hr.sub_sub_le_mul_sq (M := M') (hI i) (hxI i) fun s hs ↦
            hr.deriv_deriv_le_div_rpow (Set.ordConnected_Ioo.uIcc_subset (hI i) (hxI i) hs)
              (half_pos hψ') ((le_min (hlow γ hγ i) (by linarith [hx i])).trans hs.1)
          simpa only [add_sub_cancel_left] using h1
      _ = M' / 2 * γ ^ 2 * ∑ i, d i ^ 2 := by
          rw [mul_sum]
          exact sum_congr rfl fun i _ ↦ by ring
      _ ≤ M' / 2 * γ ^ 2 * (1 / 2) := mul_le_mul_of_nonneg_left hdsq (by positivity)
      _ = M' / 2 / 2 * γ ^ 2 := by ring
  have h6 := neg_max_le_mul_sum_of_isApproxMirrorDescentStep h hψ'.le hS hQ
  rw [show 2 * (M' / 2) * ε = M' * ε by ring] at h6
  have hGd : ∑ i, (η * ℓ i + deriv r (x i) - deriv r (a i)) * d i = Gv / N := by
    simp only [hd, hGv, sum_div, mul_div_assoc]
  rw [hGd] at h6
  set s := √(M' * ε) with hs
  have hs0 : 0 ≤ s := sqrt_nonneg _
  have hψs : 0 ≤ ψ' * s := mul_nonneg hψ'.le hs0
  have hmax : max (ψ' * s) (2 * ε) ≤ ψ' * s + 2 * ε :=
    max_le (by linarith) (by linarith)
  have h6' : -(ψ' * s + 2 * ε) ≤ ψ' * (Gv / N) := (neg_le_neg hmax).trans h6
  have h7 : ψ' * (-(s + 2 * ε / ψ') * N) ≤ ψ' * Gv := by
    have e1 : ψ' * (-(s + 2 * ε / ψ') * N) = -(ψ' * s + 2 * ε) * N := by
      field_simp
    have e2 : ψ' * Gv = ψ' * (Gv / N) * N := by field_simp
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right h6' hN0
  have h8 := le_of_mul_le_mul_left h7 hψ'
  rw [hG]
  linarith

end Schlisselberg2026Hidden
