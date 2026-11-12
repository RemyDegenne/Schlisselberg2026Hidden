/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent
public import Schlisselberg2026Hidden.ForLMLExplore.Analysis.Convex.PowerBarrier
public import LMLExplore.Analysis.Convex.Simplex
public import Schlisselberg2026Hidden.SSKM2026.BarrierUpper.Constants
public import Schlisselberg2026Hidden.SSKM2026.BarrierUpper.Lemma26
public import Schlisselberg2026Hidden.SSKM2026.BarrierUpper.Lemma27
public import Schlisselberg2026Hidden.SSKM2026.BarrierUpper.Lemma42

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
positive coordinates, or `r` to be right-continuous at `0` and left-continuous at `1` (for the log
barrier, the paper's bound is `+∞` at the boundary). The definition of a power barrier constrains
`r` on `(0, 1)` only, and `r 1` enters `D_R(u, w₁)` when `u` is a vertex of the simplex: the
statement frozen at the end of phase 1 asked right-continuity at `0` only, which is false
(`notes/statement-corrections.md`, Theorem 6).

## Main statements

* `Schlisselberg2026Hidden.regret_le_sub_div_add_of_isPowerBarrier`: [SSKM26, Theorem 6], the core
  form, for any initial point with positive coordinates and `η ≤ 2`, with
  `D_R(u, a 0) - D_R(u, a T)`, in which the value `r (u i)` cancels.
* `Schlisselberg2026Hidden.approxMirrorDescent_regret_le_of_isPowerBarrier`:
  [SSKM26, Theorem 6], corrected, for comparators with positive coordinates, or for every
  comparator when `r` is continuous at `0` and `1` within `[0, 1]`.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α] {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- In dimension `1`, a point of the simplex is the constant function `1`. -/
lemma eq_one_of_mem_simplex_of_card_eq_one (h1 : Fintype.card α = 1) {w : α → ℝ}
    (hw : w ∈ simplex α) : w = fun _ ↦ 1 := by
  obtain ⟨i₀, hi₀⟩ := Fintype.card_eq_one_iff.mp h1
  ext i
  have h := (mem_simplex_iff.mp hw).2
  rw [Fintype.sum_eq_single i₀ fun j hj ↦ absurd (hi₀ j) hj] at h
  rw [hi₀ i, h]

/-- **Theorem 6 of [SSKM26], core form.** Let `K = {w | w ≥ 0, A w = b}` be contained in the
simplex of dimension at least `2`, `r` a power barrier with exponent `ν > 1` and constants `c₁, c₂`,
`0 < η ≤ 2`, and losses in `[-1, 1]^d`. Let `a` be an `ε`-approximate trajectory of mirror descent
on the points of `K` with positive coordinates, with the potential `R w = ∑ i, r (w i)`, started at
a point of `K` with coordinates at least `m > 0`. Let `ψ > 0` satisfy
`(2 / m)^{ν-1} + 8 (ν - 1) η T / (c₁ m) ≤ ψ^{1-ν}` and let
`ε ≤ η⁴ ψ^ν / (4^{ν+2} max (1, c₂))`. Then for every `u ∈ K`,
`Regret_T(u) ≤ (D_R(u, a 0) - D_R(u, a T)) / η + (1 + 1/c₁) η T`. The value `r (u i)` cancels, so
that no hypothesis on `r 0` or `r 1` is needed. The initial point need not be uniform, as the
footnote of [SSKM26, Theorem 6] remarks. -/
lemma regret_le_sub_div_add_of_isPowerBarrier (h2 : 2 ≤ Fintype.card α) {ν c₁ c₂ : ℝ}
    {r : ℝ → ℝ} (hr : IsPowerBarrier ν c₁ c₂ r) (hν : 1 < ν) {A : (α → ℝ) →ₗ[ℝ] M} {b : M}
    (hK : {w | (∀ i, 0 ≤ w i) ∧ A w = b} ⊆ simplex α) {η ε : ℝ} (hη : 0 < η) (hη2 : η ≤ 2)
    {T : ℕ} {ℓ : ℕ → α → ℝ} (hℓ : ∀ t < T, ∀ i, |ℓ t i| ≤ 1) {m ψ : ℝ} (hm : 0 < m)
    (hψ : 0 < ψ) (hψΨ : (2 / m) ^ (ν - 1) + 8 * (ν - 1) * η * T / (c₁ * m) ≤ ψ ^ (1 - ν))
    (hε : ε ≤ η ^ 4 * ψ ^ ν / (4 ^ (ν + 2) * max 1 c₂)) {a : ℕ → α → ℝ}
    (hq : a 0 ∈ {w : α → ℝ | (∀ i, 0 < w i) ∧ A w = b}) (hmq : ∀ i, m ≤ a 0 i)
    (ha : ∀ t < T, IsApproxMirrorDescentStep {w | (∀ i, 0 < w i) ∧ A w = b}
      (fun w ↦ ∑ i, r (w i)) η (∑ i, ℓ t i • ContinuousLinearMap.proj i) (a t)
      (∑ i, deriv r (a t i) • ContinuousLinearMap.proj i) ε (a (t + 1)))
    {u : α → ℝ} (hu : u ∈ {w : α → ℝ | (∀ i, 0 ≤ w i) ∧ A w = b}) :
    regret (fun t w ↦ ∑ i, ℓ t i * w i) a u T ≤
      (bregDiv (fun w ↦ ∑ i, r (w i)) u (a 0)
          (∑ i, deriv r (a 0 i) • ContinuousLinearMap.proj i : (α → ℝ) →L[ℝ] ℝ) -
        bregDiv (fun w ↦ ∑ i, r (w i)) u (a T)
          (∑ i, deriv r (a T i) • ContinuousLinearMap.proj i : (α → ℝ) →L[ℝ] ℝ)) / η +
        (1 + 1 / c₁) * η * T := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp [regret_def]
  have hε0 := (ha 0 hT).nonneg
  have hψΨ' : (2 / m) ^ (ν - 1) + 2 * (ν - 1) * (4 * η * T) / (c₁ * m) ≤ ψ ^ (1 - ν) := by
    convert hψΨ using 2
    ring
  have hκ : 0 ≤ 4 * η * T := by positivity
  have hψm := le_half_of_add_le_rpow hr.pos hν hm hκ hψΨ'
  have hqI := mem_Ioo_of_mem_polytope h2 hK hq
  obtain ⟨i₀⟩ : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  have hψ1 : ψ ≤ 1 := by linarith [hmq i₀, (hqI i₀).2]
  obtain ⟨hδ, hεψ, hE3, hE4⟩ :=
    barrier_constants hr.one_le hr.upper_pos hη hη2 hψ hψ1 hε0 hε
  have hlow : ∀ t ≤ T, ∀ i, ψ ≤ a t i := fun t ht i ↦
    le_of_forall_isApproxMirrorDescentStep h2 hr hν hK hℓ hη ha hq hm hmq hψ hψΨ' hδ hεψ ht i
  have hmem : ∀ t ≤ T, a t ∈ {w : α → ℝ | (∀ i, 0 < w i) ∧ A w = b} := fun t ht ↦ by
    cases t with
    | zero => exact hq
    | succ s => exact (ha s (by omega)).mem
  have hsum : ∀ t ≤ T, ∑ i, a t i = 1 := fun t ht ↦
    (mem_simplex_iff.mp (hK ⟨fun j ↦ ((hmem t ht).1 j).le, (hmem t ht).2⟩)).2
  set D : ℕ → ℝ := fun t ↦ bregDiv (fun w ↦ ∑ i, r (w i)) u (a t)
    (∑ i, deriv r (a t i) • ContinuousLinearMap.proj i : (α → ℝ) →L[ℝ] ℝ) with hD
  have hround : ∀ t < T, ∑ i, ℓ t i * a t i - ∑ i, ℓ t i * u i ≤
      η / c₁ + η + (D t - D (t + 1)) / η := by
    intro t ht
    have h12 := sum_mul_sub_sub_bregDiv_div_le hr (mem_Ioo_of_mem_polytope h2 hK (hmem t ht.le))
      (mem_Ioo_of_mem_polytope h2 hK (hmem (t + 1) ht)) (hsum t ht.le) (hsum (t + 1) ht)
      (hℓ t ht) hη
    have h13 := mul_sum_mul_sub_le_of_isApproxMirrorDescentStep h2 hr hK (ha t ht) hψ
      (hlow (t + 1) ht) hE3 hE4 hu
    set E := bregDiv (fun w : α → ℝ ↦ ∑ i, r (w i)) (a (t + 1)) (a t)
      (∑ i, deriv r (a t i) • ContinuousLinearMap.proj i : (α → ℝ) →L[ℝ] ℝ) with hE
    simp only [mul_sub, sum_sub_distrib] at h12 h13
    have hc₁ := hr.pos
    have h12' := mul_le_mul_of_nonneg_left h12 hη.le
    rw [mul_sub, mul_div_cancel₀ E hη.ne'] at h12'
    have e : η / c₁ + η + (D t - D (t + 1)) / η =
        (η * (η / c₁) + η ^ 2 + (D t - D (t + 1))) / η := by
      field_simp
    rw [e, le_div_iff₀ hη]
    linarith
  calc regret (fun t w ↦ ∑ i, ℓ t i * w i) a u T
      = ∑ t ∈ range T, (∑ i, ℓ t i * a t i - ∑ i, ℓ t i * u i) := regret_def _ _ _ _
    _ ≤ ∑ t ∈ range T, (η / c₁ + η + (D t - D (t + 1)) / η) :=
        sum_le_sum fun t ht ↦ hround t (mem_range.mp ht)
    _ = (D 0 - D T) / η + (1 + 1 / c₁) * η * T := by
        rw [sum_add_distrib, sum_const, card_range, ← sum_div, sum_range_sub', nsmul_eq_mul]
        ring

/-- **Polynomially small errors suffice for power barriers** [SSKM26, Theorem 6], with corrected
constants. Let `r` be a power barrier with exponent `ν > 1` and constants `c₁, c₂`, and let
`K = {w | w ≥ 0, A w = b}` be contained in the simplex and contain the uniform point. Let `η > 0`,
let the losses have coordinates in `[-1, 1]`, and let
`ε ≤ η⁴ Ψ^{-ν/(ν-1)} / (4^{ν+2} max (1, c₂))` with `Ψ = (2d)^{ν-1} + 8 (ν - 1) η T d / c₁` and
`d` the number of coordinates. Then every `ε`-approximate trajectory `a` of mirror descent on `K`
with potential `w ↦ ∑ i, r (w i)` and learning rate `η`, taken on the points of `K` with positive
coordinates and started at the uniform point, has regret at most
`D_R(u, a 0) / η + (1 + 1/c₁) η T` against every `u ∈ K` with positive coordinates, and against
every `u ∈ K` if `r` is right-continuous at `0` and left-continuous at `1`.

The definition of a power barrier constrains `r` on `(0, 1)` only, and the values `r 0` and `r 1`
enter `D_R(u, a 0)` when `u` has a zero coordinate or is a vertex of the simplex. The statement
frozen at the end of phase 1 asked right-continuity at `0` only, which is false
(`exists_not_regret_le_of_isPowerBarrier`); the continuity at `1` was added on 2026-11-12
(`notes/statement-corrections.md`, Theorem 6). -/
theorem approxMirrorDescent_regret_le_of_isPowerBarrier {ν c₁ c₂ : ℝ}
    {r : ℝ → ℝ} (hr : IsPowerBarrier ν c₁ c₂ r) (hν : 1 < ν) (A : (α → ℝ) →ₗ[ℝ] M) (b : M)
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
    (hu' : (∀ i, 0 < u i) ∨
      (ContinuousWithinAt r (Set.Ici 0) 0 ∧ ContinuousWithinAt r (Set.Iic 1) 1)) :
    regret (fun t w ↦ ∑ i, ℓ t i * w i) a u T ≤
      bregDiv (fun w ↦ ∑ i, r (w i)) u (a 0)
          (∑ i, deriv r (a 0 i) • ContinuousLinearMap.proj i : (α → ℝ) →L[ℝ] ℝ) / η +
        (1 + 1 / c₁) * η * T := by
  set d := Fintype.card α with hd
  have hc₁ := hr.pos
  have hmemK : ∀ t < T + 1, a t ∈ {w : α → ℝ | (∀ i, 0 ≤ w i) ∧ A w = b} := fun t ht ↦ by
    cases t with
    | zero => rw [ha0]; exact hunif
    | succ s =>
      have h := (ha s (by omega)).mem
      exact ⟨fun j ↦ (h.1 j).le, h.2⟩
  have hd1 : 1 ≤ d := by
    by_contra! h
    have h0 : d = 0 := by omega
    have := (mem_simplex_iff.mp (hK hunif)).2
    simp [h0] at this
  have hRHS0 : 0 ≤ (1 + 1 / c₁) * η * T := by positivity
  rcases hd1.eq_or_lt with hd1 | hd2
  · -- dimension `1`: every iterate is the comparator
    have h1 := eq_one_of_mem_simplex_of_card_eq_one hd1.symm (hK hu)
    have hreg : regret (fun t w ↦ ∑ i, ℓ t i * w i) a u T = 0 := by
      rw [regret_def]
      refine sum_eq_zero fun t ht ↦ ?_
      rw [eq_one_of_mem_simplex_of_card_eq_one hd1.symm
        (hK (hmemK t (by have := mem_range.mp ht; omega))), h1, sub_self]
    have hu0 : u = a 0 := by
      rw [h1, eq_one_of_mem_simplex_of_card_eq_one hd1.symm (hK (hmemK 0 (by omega)))]
    rw [hreg, hu0]
    simp only [bregDiv, sub_self, map_zero, zero_div, zero_add]
    exact hRHS0
  have h2 : 2 ≤ d := hd2
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hq : a 0 ∈ {w : α → ℝ | (∀ i, 0 < w i) ∧ A w = b} := by
    rw [ha0]
    exact ⟨fun _ ↦ inv_pos.mpr hdpos, hunif.2⟩
  have hqI := mem_Ioo_of_mem_polytope h2 hK hq
  -- the divergences from `u` are nonnegative
  have hDnonneg : ∀ y ∈ {w : α → ℝ | (∀ i, 0 < w i) ∧ A w = b},
      0 ≤ bregDiv (fun w ↦ ∑ i, r (w i)) u y
        (∑ i, deriv r (y i) • ContinuousLinearMap.proj i : (α → ℝ) →L[ℝ] ℝ) := by
    intro y hy
    have hyI := mem_Ioo_of_mem_polytope h2 hK hy
    rw [bregDiv_sum_apply]
    refine sum_nonneg fun i _ ↦ ?_
    rcases hu' with hu' | ⟨hc₀, hc₁'⟩
    · exact hr.sub_sub_nonneg (mem_Ioo_of_mem_polytope h2 hK ⟨hu', hu.2⟩ i) (hyI i)
    · have hu1 : u i ≤ 1 := by
        have h := (mem_simplex_iff.mp (hK hu))
        rw [← h.2]
        exact single_le_sum (fun j _ ↦ h.1 j) (mem_univ i)
      exact hr.sub_sub_nonneg_of_mem_Icc hc₀ hc₁' ⟨hu.1 i, hu1⟩ (hyI i)
  rcases le_or_gt η 2 with hη2 | hη2
  · -- the main case
    set Ψ := (2 * (d : ℝ)) ^ (ν - 1) + 8 * (ν - 1) * η * T * d / c₁ with hΨ
    have hν1 : 0 < ν - 1 := sub_pos.mpr hν
    have hΨ0 : 0 < Ψ := by
      have : 0 < (2 * (d : ℝ)) ^ (ν - 1) := rpow_pos_of_pos (by positivity) _
      positivity
    set ψ := Ψ ^ (-1 / (ν - 1)) with hψ
    have hψ0 : 0 < ψ := rpow_pos_of_pos hΨ0 _
    have hψΨ : ψ ^ (1 - ν) = Ψ := by
      rw [hψ, ← rpow_mul hΨ0.le, show -1 / (ν - 1) * (1 - ν) = 1 by field_simp; ring, rpow_one]
    have hψν : ψ ^ ν = Ψ ^ (-(ν / (ν - 1))) := by
      rw [hψ, ← rpow_mul hΨ0.le]
      congr 1
      field_simp
    have hcore := regret_le_sub_div_add_of_isPowerBarrier h2 hr hν hK hη hη2 hℓ
      (m := (d : ℝ)⁻¹) (ψ := ψ) (inv_pos.mpr hdpos) hψ0 (by
        rw [hψΨ, hΨ, div_inv_eq_mul]
        field_simp
        rfl) (by rwa [hψν]) hq (fun i ↦ by rw [ha0]) ha hu
    have hT := hDnonneg (a T) (by
      rcases Nat.eq_zero_or_pos T with h | h
      · rw [h]; exact hq
      · obtain ⟨s, rfl⟩ : ∃ s, T = s + 1 := ⟨T - 1, by omega⟩
        exact (ha s (by omega)).mem)
    refine hcore.trans ?_
    gcongr
    linarith
  · -- large learning rates: the regret is at most `2 T`
    have hreg : regret (fun t w ↦ ∑ i, ℓ t i * w i) a u T ≤ 2 * T := by
      rw [regret_def]
      calc ∑ t ∈ range T, (∑ i, ℓ t i * a t i - ∑ i, ℓ t i * u i)
          ≤ ∑ _t ∈ range T, (2 : ℝ) := sum_le_sum fun t ht ↦ by
            have ht := mem_range.mp ht
            have h1 := sum_mul_le_sum_abs (hℓ t ht) (fun i ↦ a t i - u i)
            have h3 := sum_abs_sub_le_two_of_mem_simplex (hK (hmemK t (by omega))) (hK hu)
            simp only [mul_sub, sum_sub_distrib] at h1
            linarith
        _ = 2 * T := by rw [sum_const, card_range, nsmul_eq_mul]; ring
    have h0 := hDnonneg (a 0) hq
    have h1 : 0 ≤ bregDiv (fun w ↦ ∑ i, r (w i)) u (a 0)
        (∑ i, deriv r (a 0 i) • ContinuousLinearMap.proj i : (α → ℝ) →L[ℝ] ℝ) / η :=
      div_nonneg h0 hη.le
    have h2 : 2 * (T : ℝ) ≤ (1 + 1 / c₁) * η * T := by
      have h3 : 0 < η * (1 / c₁) := by positivity
      have h4 : 2 ≤ (1 + 1 / c₁) * η := by linarith
      exact mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg T)
    linarith

end Schlisselberg2026Hidden
