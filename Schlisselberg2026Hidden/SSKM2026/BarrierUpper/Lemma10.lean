/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.SSKM2026.BarrierUpper.Lemma11

/-!
# Lemma 10 of [SSKM26], corrected: the balance of an approximate trajectory

Let `K = {w | w ≥ 0, A w = b}` be contained in the simplex of dimension at least `2`, `r` a power
barrier, and `a` an `ε`-approximate trajectory of mirror descent on the points of `K` with positive
coordinates, with the potential `R w = ∑ i, r (w i)` and losses in `[-1, 1]^d`. If the iterates
`a 1, …, a t` have coordinates at least `ψ' > 0`, the balance of the trajectory is at most linear
in `t`: for all `y, z ∈ K`,
`⟨∇R(a 0) - ∇R(a t), y - z⟩ ≤ t (η + √(c₂ (ψ' / 2)^{-ν} ε) + 2 ε / ψ') ‖y - z‖₁`.

The proof telescopes the one-step bound of `sum_deriv_sub_mul_le_of_isApproxMirrorDescentStep`.
For exact steps, [SSKM26, Lemma 10] states the identity with the losses `ℓ_{t₁:t₂}`, while the
balance between the rounds `t₁` and `t₂` uses the losses `ℓ_{t₁:t₂-1}` (`notes/paper-errata.md`).

## Main statements

* `Schlisselberg2026Hidden.sum_deriv_sub_mul_le_of_forall_isApproxMirrorDescentStep`:
  [SSKM26, Lemma 10], corrected.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α] {M : Type*} [AddCommGroup M] [Module ℝ M]
  {ν c₁ c₂ : ℝ} {r : ℝ → ℝ} {A : (α → ℝ) →ₗ[ℝ] M} {b : M} {η ε : ℝ}

/-- **The balance of an approximate trajectory** [SSKM26, Lemma 10], corrected. Let
`K = {w | w ≥ 0, A w = b}` be contained in the simplex of dimension at least `2`, `r` a power
barrier, `η ≥ 0`, and let `a 1, …, a t` be `ε`-approximate steps of mirror descent on the points of
`K` with positive coordinates, with the potential `w ↦ ∑ i, r (w i)` and losses in `[-1, 1]^d`. If
their coordinates are at least `ψ' > 0`, then for all `y, z ∈ K`,
`⟨∇R(a 0) - ∇R(a t), y - z⟩ ≤ t (η + √(c₂ / (ψ' / 2)^ν ε) + 2 ε / ψ') ‖y - z‖₁`. -/
lemma sum_deriv_sub_mul_le_of_forall_isApproxMirrorDescentStep (h2 : 2 ≤ Fintype.card α)
    (hr : IsPowerBarrier ν c₁ c₂ r) (hK : {w | (∀ i, 0 ≤ w i) ∧ A w = b} ⊆ simplex α)
    {ℓ a : ℕ → α → ℝ} {t : ℕ} (hℓ : ∀ s < t, ∀ i, |ℓ s i| ≤ 1) (hη : 0 ≤ η)
    (ha : ∀ s < t, IsApproxMirrorDescentStep {w | (∀ i, 0 < w i) ∧ A w = b}
      (fun w ↦ ∑ i, r (w i)) η (∑ i, ℓ s i • ContinuousLinearMap.proj i) (a s)
      (∑ i, deriv r (a s i) • ContinuousLinearMap.proj i) ε (a (s + 1)))
    {ψ' : ℝ} (hψ' : 0 < ψ') (hpos : ∀ s < t, ∀ i, ψ' ≤ a (s + 1) i) {y z : α → ℝ}
    (hy : y ∈ {w : α → ℝ | (∀ i, 0 ≤ w i) ∧ A w = b})
    (hz : z ∈ {w : α → ℝ | (∀ i, 0 ≤ w i) ∧ A w = b}) :
    ∑ i, (deriv r (a 0 i) - deriv r (a t i)) * (y i - z i) ≤
      t * (η + √(c₂ / (ψ' / 2) ^ ν * ε) + 2 * ε / ψ') * ∑ i, |y i - z i| := by
  set F : ℕ → ℝ := fun s ↦ ∑ i, deriv r (a s i) * (y i - z i) with hF
  have hFs (s : ℕ) : F s - F (s + 1) =
      ∑ i, (deriv r (a s i) - deriv r (a (s + 1) i)) * (y i - z i) := by
    simp only [hF, ← sum_sub_distrib, sub_mul]
  have h1 : ∑ i, (deriv r (a 0 i) - deriv r (a t i)) * (y i - z i) =
      ∑ s ∈ range t, (F s - F (s + 1)) := by
    rw [sum_range_sub']
    simp only [hF, ← sum_sub_distrib, sub_mul]
  rw [h1]
  calc ∑ s ∈ range t, (F s - F (s + 1))
      ≤ ∑ _s ∈ range t, (η + √(c₂ / (ψ' / 2) ^ ν * ε) + 2 * ε / ψ') * ∑ i, |y i - z i| :=
        sum_le_sum fun s hs ↦ by
          have hs := mem_range.mp hs
          have h3 := sum_deriv_sub_mul_le_of_isApproxMirrorDescentStep h2 hr hK (ha s hs) hψ'
            (hpos s hs) hy hz
          have h4 := mul_le_mul_of_nonneg_left
            (sum_mul_le_sum_abs (hℓ s hs) (fun i ↦ y i - z i)) hη
          rw [hFs]
          linarith
    _ = t * (η + √(c₂ / (ψ' / 2) ^ ν * ε) + 2 * ε / ψ') * ∑ i, |y i - z i| := by
        rw [sum_const, card_range, nsmul_eq_mul]
        ring

end Schlisselberg2026Hidden
