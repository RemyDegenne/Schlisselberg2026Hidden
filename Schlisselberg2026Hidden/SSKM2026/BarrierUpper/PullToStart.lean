/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.SSKM2026.BarrierUpper.Lemma10
public import Schlisselberg2026Hidden.SSKM2026.BarrierUpper.Lemma12

/-!
# A step can at most halve a coordinate (replaces Lemma 25 of [SSKM26] on polytopes)

Let `K = {w | w ≥ 0, A w = b}` be contained in the simplex of dimension at least `2`, `r` a power
barrier with exponent `ν > 1`, and `a` an `ε`-approximate trajectory of mirror descent on the
points of `K` with positive coordinates, started at `q = a 0` with coordinates at least `m > 0`.
Let `ψ > 0` satisfy `(2 / m)^{ν-1} + 8 (ν - 1) η T / (c₁ m) ≤ ψ^{1-ν}`, and let `ε` be small:
the per-round balance error `δ = √(c₂ (ψ / 4)^{-ν} ε) + 4 ε / ψ` is at most `η` and `ε ≤ η ψ`.
If the iterates `a 1, …, a t` have coordinates at least `ψ / 2`, then so has `a (t + 1)`.

The proof compares `x = a (t + 1)` with the point `z = x + (ψ / 2) (q - x)` of the segment towards
the start, which lies in `K` by convexity. The step condition at `z` and the convexity of the
objective bound the derivative of the objective at `z` towards `q`; the balance of the trajectory
(`sum_deriv_sub_mul_le_of_forall_isApproxMirrorDescentStep`) then bounds
`S_q(z) = ⟨∇R(q) - ∇R(z), q - z⟩` by `4 η T`, so that the coordinates of `z` are at least `ψ`
(`le_of_sum_deriv_sub_mul_sub_le`), and those of `x` at least `ψ / 2`.

[SSKM26] proves this step with Lemma 25, which compares the step with a point that moves mass
between two coordinates: on a polytope this point leaves `K`, and Lemma 25 is proved on the
simplex only (`notes/paper-errata.md`). The argument here needs no exact minimizer, no
smoothness and no condition on `η`.

## Main statements

* `Schlisselberg2026Hidden.half_le_of_forall_isApproxMirrorDescentStep`: a step from a trajectory
  whose iterates have coordinates at least `ψ / 2` has coordinates at least `ψ / 2`.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α] {M : Type*} [AddCommGroup M] [Module ℝ M]
  {ν c₁ c₂ : ℝ} {r : ℝ → ℝ} {A : (α → ℝ) →ₗ[ℝ] M} {b : M} {η ε : ℝ}

/-- **A step can at most halve a coordinate**, the step that replaces Lemma 25 of [SSKM26] on
polytopes. Let `K = {w | w ≥ 0, A w = b}` be contained in the simplex of dimension at least `2`,
`r` a power barrier with exponent `ν > 1`, `η > 0`, and `a` an `ε`-approximate trajectory of
mirror descent on the points of `K` with positive coordinates for `T` rounds, with losses in
`[-1, 1]^d`, started at a point of `K` with positive coordinates at least `m > 0`. Let `ψ > 0`
satisfy `(2 / m)^{ν-1} + 2 (ν - 1) (4 η T) / (c₁ m) ≤ ψ^{1-ν}`, and let
`√(c₂ / (ψ / 4)^ν ε) + 4 ε / ψ ≤ η` and `ε ≤ η ψ`. If `t < T` and the iterates `a 1, …, a t` have
coordinates at least `ψ / 2`, then so has `a (t + 1)`. -/
lemma half_le_of_forall_isApproxMirrorDescentStep (h2 : 2 ≤ Fintype.card α)
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
    {t : ℕ} (ht : t < T) (hprev : ∀ s < t, ∀ i, ψ / 2 ≤ a (s + 1) i) (i : α) :
    ψ / 2 ≤ a (t + 1) i := by
  set q := a 0 with hq_def
  set x := a (t + 1) with hx_def
  set lam := ψ / 2 with hlam
  have hstep := ha t ht
  have hε := hstep.nonneg
  have hx := hstep.mem
  have hxI := mem_Ioo_of_mem_polytope h2 hK hx
  have hqI := mem_Ioo_of_mem_polytope h2 hK hq
  have hqK : q ∈ {w : α → ℝ | (∀ i, 0 ≤ w i) ∧ A w = b} := ⟨fun j ↦ (hq.1 j).le, hq.2⟩
  have hxK : x ∈ {w : α → ℝ | (∀ i, 0 ≤ w i) ∧ A w = b} := ⟨fun j ↦ (hx.1 j).le, hx.2⟩
  have hκ : 0 ≤ 4 * η * T := by positivity
  have hψm := le_half_of_add_le_rpow hr.pos hν hm hκ hψΨ
  obtain ⟨i₀⟩ : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  have hm1 : m < 1 := (hmq i₀).trans_lt (hqI i₀).2
  have hlam0 : 0 < lam := half_pos hψ
  have hlam1 : lam < 1 := by linarith
  -- the point `z` of the segment from `x` to `q`
  set z : α → ℝ := fun j ↦ x j + lam * (q j - x j) with hz_def
  have hz : z ∈ {w : α → ℝ | (∀ i, 0 < w i) ∧ A w = b} := by
    refine ⟨fun j ↦ ?_, ?_⟩
    · have : z j = (1 - lam) * x j + lam * q j := by simp only [hz_def]; ring
      rw [this]
      have := (hx.1 j)
      have := (hq.1 j)
      have : 0 < 1 - lam := by linarith
      positivity
    · have : z = x + lam • (q - x) := by
        ext j
        simp [hz_def]
      rw [this]
      exact apply_add_smul_sub_eq hx.2 hq.2 hx.2 _
  have hzI := mem_Ioo_of_mem_polytope h2 hK hz
  -- the step condition at `z` and the convexity of the objective
  set Gq := ∑ j, (η * ℓ t j + deriv r (z j) - deriv r (a t j)) * (q j - x j) with hGq
  have h1 := sum_le_of_isApproxMirrorDescentStep hstep hz
  have hDxz : 0 ≤ ∑ j, (r (x j) - r (z j) - deriv r (z j) * (x j - z j)) :=
    sum_nonneg fun j _ ↦ hr.sub_sub_nonneg (hxI j) (hzI j)
  have hkey : (η * ∑ j, ℓ t j * x j +
      ∑ j, (r (x j) - r (a t j) - deriv r (a t j) * (x j - a t j))) -
      (η * ∑ j, ℓ t j * z j + ∑ j, (r (z j) - r (a t j) - deriv r (a t j) * (z j - a t j))) =
      ∑ j, (r (x j) - r (z j) - deriv r (z j) * (x j - z j)) - lam * Gq := by
    simp only [hGq, mul_sum, ← sum_sub_distrib, ← sum_add_distrib, hz_def]
    refine sum_congr rfl fun j _ ↦ ?_
    ring
  have hG1 : -ε ≤ lam * Gq := by linarith
  -- splitting the derivative at `z`
  set S := ∑ j, (deriv r (q j) - deriv r (z j)) * (q j - z j) with hS
  set N := ∑ j, |q j - x j| with hN
  have hS0 : 0 ≤ S := sum_nonneg fun j _ ↦ deriv_sub_mul_sub_nonneg hr (hqI j) (hzI j)
  have hN0 : 0 ≤ N := sum_nonneg fun j _ ↦ abs_nonneg _
  have hN2 : N ≤ 2 := sum_abs_sub_le_two_of_mem_simplex (hK hqK) (hK hxK)
  set Lq := ∑ j, ℓ t j * (q j - x j) with hLq
  set B := ∑ j, (deriv r (q j) - deriv r (a t j)) * (q j - x j) with hB
  have hsplit : (1 - lam) * Gq = (1 - lam) * (η * Lq) + (1 - lam) * B - S := by
    simp only [hGq, hLq, hB, hS, mul_sum, ← sum_add_distrib, ← sum_sub_distrib, hz_def]
    refine sum_congr rfl fun j _ ↦ ?_
    ring
  have hLq_le : η * Lq ≤ η * N :=
    mul_le_mul_of_nonneg_left (sum_mul_le_sum_abs (hℓ t ht) _) hη.le
  have hB_le : B ≤ t * (2 * η) * N := by
    have h3 := sum_deriv_sub_mul_le_of_forall_isApproxMirrorDescentStep h2 hr hK
      (fun s hs ↦ hℓ s (hs.trans ht)) hη.le (fun s hs ↦ ha s (hs.trans ht)) hlam0 hprev hqK hxK
    have h4 : (t : ℝ) * (η + √(c₂ / (lam / 2) ^ ν * ε) + 2 * ε / lam) * N ≤
        t * (2 * η) * N := by
      gcongr
      linarith
    exact h3.trans h4
  -- `S ≤ 4 η T`
  have h1lam : 0 < 1 - lam := by linarith
  have hA : η * Lq + B ≤ 2 * η + 4 * η * t := by
    have h3 : η * N ≤ η * 2 := mul_le_mul_of_nonneg_left hN2 hη.le
    have h4 : t * (2 * η) * N ≤ t * (2 * η) * 2 := mul_le_mul_of_nonneg_left hN2 (by positivity)
    linarith
  have hA' : (1 - lam) * (η * Lq + B) ≤ 2 * η + 4 * η * t := by
    rcases le_total 0 (η * Lq + B) with h | h
    · have := mul_nonneg hlam0.le h
      linarith
    · have := mul_nonpos_of_nonneg_of_nonpos h1lam.le h
      have : 0 ≤ 2 * η + 4 * η * t := by positivity
      linarith
  have hlamS : lam * S ≤ lam * (4 * η * T) := by
    have h5 : -(1 - lam) * ε ≤ lam * ((1 - lam) * Gq) := by
      have := mul_le_mul_of_nonneg_left hG1 h1lam.le
      linarith
    rw [hsplit] at h5
    have h5' : lam * S ≤ (1 - lam) * ε + lam * ((1 - lam) * (η * Lq + B)) := by linarith
    have h6 : ε ≤ 2 * lam * η := by rw [hlam]; linarith
    have h7 : (t : ℝ) + 1 ≤ T := by exact_mod_cast ht
    have h8 : (1 - lam) * ε ≤ ε := by
      have := mul_nonneg hlam0.le hε
      linarith
    have h9 : lam * ((1 - lam) * (η * Lq + B)) ≤ lam * (2 * η + 4 * η * t) :=
      mul_le_mul_of_nonneg_left hA' hlam0.le
    have h10 : lam * (4 * η + 4 * η * t) ≤ lam * (4 * η * T) := by
      refine mul_le_mul_of_nonneg_left ?_ hlam0.le
      have := mul_le_mul_of_nonneg_left h7 hη.le
      linarith
    linarith
  have hS4 : S ≤ 4 * η * T := le_of_mul_le_mul_left hlamS hlam0
  -- the coordinates of `z` are at least `ψ`, those of `x` at least `ψ / 2`
  have hzψ := le_of_sum_deriv_sub_mul_sub_le hr hν hqI hzI hm hmq hκ hψΨ hS4 i
  have hzi : z i = (1 - lam) * x i + lam * q i := by simp only [hz_def]; ring
  have h1 : lam * q i ≤ lam := mul_le_of_le_one_right hlam0.le (hqI i).2.le
  have h2 : 0 ≤ lam * x i := mul_nonneg hlam0.le (hxI i).1.le
  have h3 : ψ = 2 * lam := by rw [hlam]; ring
  linarith

end Schlisselberg2026Hidden
