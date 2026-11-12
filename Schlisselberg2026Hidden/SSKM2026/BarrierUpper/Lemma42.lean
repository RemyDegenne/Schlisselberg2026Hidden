/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.SSKM2026.BarrierUpper.PullToStart

/-!
# Lemma 42 of [SSKM26], corrected: the iterates stay away from the boundary

Let `K = {w | w ≥ 0, A w = b}` be contained in the simplex of dimension at least `2`, `r` a power
barrier with exponent `ν > 1`, and `a` an `ε`-approximate trajectory of mirror descent on the
points of `K` with positive coordinates for `T` rounds, with losses in `[-1, 1]^d`, started at a
point with coordinates at least `m > 0`. If `ψ > 0` satisfies
`(2 / m)^{ν-1} + 8 (ν - 1) η T / (c₁ m) ≤ ψ^{1-ν}`, the per-round balance error
`√(c₂ (ψ / 4)^{-ν} ε) + 4 ε / ψ` is at most `η` and `ε ≤ η ψ`, then every coordinate of
`a 0, …, a T` is at least `ψ`.

The proof is an induction on the rounds: a step at most halves a coordinate
(`half_le_of_forall_isApproxMirrorDescentStep`), so the balance of the trajectory up to the new
iterate is at most `4 η T` (`sum_deriv_sub_mul_le_of_forall_isApproxMirrorDescentStep`), which
gives the lower bound `ψ` (`le_of_sum_deriv_sub_mul_sub_le`).

[SSKM26, Lemma 42] states the bound `(c₁ / (8 η T d + c₁ (2 d)^{ν-1}))^{1/(ν-1)}`, which uses
Lemma 41 without its factor `1 / (ν - 1)` and is false for `ν > 9`, already for exact steps
(`notes/paper-errata.md`).

## Main statements

* `Schlisselberg2026Hidden.le_of_forall_isApproxMirrorDescentStep`: [SSKM26, Lemma 42],
  corrected.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α] {M : Type*} [AddCommGroup M] [Module ℝ M]
  {ν c₁ c₂ : ℝ} {r : ℝ → ℝ} {A : (α → ℝ) →ₗ[ℝ] M} {b : M} {η ε : ℝ}

/-- **The iterates stay away from the boundary** [SSKM26, Lemma 42], corrected. Let
`K = {w | w ≥ 0, A w = b}` be contained in the simplex of dimension at least `2`, `r` a power
barrier with exponent `ν > 1`, `η > 0`, and `a` an `ε`-approximate trajectory of mirror descent on
the points of `K` with positive coordinates for `T` rounds, with losses in `[-1, 1]^d`, started at
a point of `K` with coordinates at least `m > 0`. Let `ψ > 0` satisfy
`(2 / m)^{ν-1} + 2 (ν - 1) (4 η T) / (c₁ m) ≤ ψ^{1-ν}`, and let
`√(c₂ / (ψ / 4)^ν ε) + 4 ε / ψ ≤ η` and `ε ≤ η ψ`. Then `ψ ≤ a t i` for every `t ≤ T`. -/
lemma le_of_forall_isApproxMirrorDescentStep (h2 : 2 ≤ Fintype.card α)
    (hr : IsPowerBarrier ν c₁ c₂ r) (hν : 1 < ν)
    (hK : {w | (∀ i, 0 ≤ w i) ∧ A w = b} ⊆ simplex α)
    {ℓ a : ℕ → α → ℝ} {T : ℕ} (hℓ : ∀ s < T, ∀ i, |ℓ s i| ≤ 1) (hη : 0 < η)
    (ha : ∀ s < T, IsApproxMirrorDescentStep {w | (∀ i, 0 < w i) ∧ A w = b}
      (fun w ↦ ∑ i, r (w i)) η (∑ i, ℓ s i • ContinuousLinearMap.proj i) (a s)
      (∑ i, deriv r (a s i) • ContinuousLinearMap.proj i) ε (a (s + 1)))
    (hq : a 0 ∈ {w : α → ℝ | (∀ i, 0 < w i) ∧ A w = b}) {m ψ : ℝ} (hm : 0 < m)
    (hmq : ∀ i, m ≤ a 0 i) (hψ : 0 < ψ)
    (hψΨ : (2 / m) ^ (ν - 1) + 2 * (ν - 1) * (4 * η * T) / (c₁ * m) ≤ ψ ^ (1 - ν))
    (hδ : √(c₂ / (ψ / 2 / 2) ^ ν * ε) + 2 * ε / (ψ / 2) ≤ η) (hεψ : ε ≤ η * ψ)
    {t : ℕ} (ht : t ≤ T) (i : α) : ψ ≤ a t i := by
  have hqI := mem_Ioo_of_mem_polytope h2 hK hq
  have hqK : a 0 ∈ {w : α → ℝ | (∀ i, 0 ≤ w i) ∧ A w = b} := ⟨fun j ↦ (hq.1 j).le, hq.2⟩
  have hκ : 0 ≤ 4 * η * T := by positivity
  have hψm := le_half_of_add_le_rpow hr.pos hν hm hκ hψΨ
  suffices H : ∀ t ≤ T, ∀ s ≤ t, ∀ i, ψ ≤ a s i from H t ht t le_rfl i
  intro t
  induction t with
  | zero =>
    intro _ s hs i
    rw [Nat.le_zero.mp hs]
    linarith [hmq i]
  | succ t ih =>
    intro ht s hs i
    have ih' := ih (by omega)
    rcases Nat.lt_or_ge s (t + 1) with hst | hst
    · exact ih' s (by omega) i
    obtain rfl : s = t + 1 := by omega
    have hprev : ∀ s < t, ∀ i, ψ / 2 ≤ a (s + 1) i := fun s hs i ↦ by
      linarith [ih' (s + 1) hs i]
    have hhalf := half_le_of_forall_isApproxMirrorDescentStep h2 hr hν hK hℓ hη ha hq hm hmq hψ
      hψΨ hδ hεψ (by omega : t < T) hprev
    have hpos : ∀ s < t + 1, ∀ i, ψ / 2 ≤ a (s + 1) i := fun s hs i ↦ by
      rcases Nat.lt_or_ge s t with h | h
      · exact hprev s h i
      · rw [show s = t by omega]
        exact hhalf i
    have hx := (ha t (by omega)).mem
    have hxK : a (t + 1) ∈ {w : α → ℝ | (∀ i, 0 ≤ w i) ∧ A w = b} :=
      ⟨fun j ↦ (hx.1 j).le, hx.2⟩
    have h3 := sum_deriv_sub_mul_le_of_forall_isApproxMirrorDescentStep h2 hr hK
      (fun s hs ↦ hℓ s (by omega)) hη.le (fun s hs ↦ ha s (by omega)) (half_pos hψ) hpos hqK hxK
    have hN2 := sum_abs_sub_le_two_of_mem_simplex (hK hqK) (hK hxK)
    have h5 : ((t + 1 : ℕ) : ℝ) ≤ T := by exact_mod_cast ht
    have h4 : ((t + 1 : ℕ) : ℝ) * (η + √(c₂ / (ψ / 2 / 2) ^ ν * ε) + 2 * ε / (ψ / 2)) *
        ∑ j, |a 0 j - a (t + 1) j| ≤ 4 * η * T := by
      calc _ ≤ ((t + 1 : ℕ) : ℝ) * (2 * η) * 2 := by
            gcongr
            linarith
        _ ≤ T * (2 * η) * 2 := by gcongr
        _ = 4 * η * T := by ring
    exact le_of_sum_deriv_sub_mul_sub_le hr hν hqI (mem_Ioo_of_mem_polytope h2 hK hx) hm hmq hκ
      hψΨ (h3.trans h4) i

end Schlisselberg2026Hidden
