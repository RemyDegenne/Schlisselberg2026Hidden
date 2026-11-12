/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.Analysis.Convex.Bregman.StrongConvex
public import LMLExplore.OnlineLearning.FTRL.Basic
public import LMLExplore.OnlineLearning.FTRL.Equality
public import Schlisselberg2026Hidden.ForLMLExplore.Analysis.Real.Sqrt

/-!
# Approximate plays of follow the regularized leader

Follow the regularized leader on a set `K` of a real normed space `E`, with potential `F`,
learning rate `η` and linear losses `y t : E →L[ℝ] ℝ`, plays at round `t` a minimizer over `K` of
`b ↦ η ∑ s < t, y s b + F b` (`LMLExplore.OnlineLearning.IsFTRLPlay`). An **`ε`-approximate
play** is a point of `K` whose objective is at most `ε` above the objective of every point of `K`
[SSKM26, Algorithm 1]. Unlike approximate mirror descent, the objective of each round does not
depend on the previous plays, so the errors of different rounds do not compound: each
approximate play is within `2 η ‖y t‖ / m + √(2 ε / m)` of the exact play of the next round, for
an `m`-strongly convex potential, and the exact plays satisfy the FTRL inequality.

## Main definitions

* `IsApproxFTRLPlay K F η y t ε x`: `x` is an `ε`-approximate play of FTRL on `K` at round `t`,
  with potential `F`, learning rate `η` and losses `y`.

## Main statements

* `isApproxFTRLPlay_zero_iff`: the `0`-approximate plays are the plays of FTRL.
* `IsApproxFTRLPlay.mono`: an `ε`-approximate play is `ε'`-approximate for `ε ≤ ε'`.
* `IsApproxFTRLPlay.nonneg`: approximate plays exist only for `ε ≥ 0`.
* `exists_isApproxFTRLPlay`: if the objective is bounded below on a nonempty `K`, then
  `ε`-approximate plays exist for every `ε > 0`.
* `IsApproxFTRLPlay.norm_sub_le`: [SSKM26, Lemma 51], for an `m`-strongly convex potential.
* `approxFTRL_sum_apply_sub_le`: [SSKM26, Theorem 52], for an `m`-strongly convex potential,
  per-round errors `ε t` and any losses.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open Finset

namespace LMLExplore.OnlineLearning

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {F : E → ℝ} {η : ℝ}
  {y : ℕ → E →L[ℝ] ℝ} {t : ℕ} {x : E} {ε ε' : ℝ}

/-- `x` is an **`ε`-approximate play of FTRL** [SSKM26, Algorithm 1] on `K` at round `t`, with
potential `F`, learning rate `η` and losses `y`: `x ∈ K`, and the objective
`b ↦ η ∑ s < t, y s b + F b` at `x` is at most `ε` above its value at every point of `K`. -/
structure IsApproxFTRLPlay (K : Set E) (F : E → ℝ) (η : ℝ) (y : ℕ → E →L[ℝ] ℝ) (t : ℕ) (ε : ℝ)
    (x : E) : Prop where
  /-- The play lies in `K`. -/
  mem : x ∈ K
  /-- The objective at the play is at most `ε` above its value at every point of `K`. -/
  le_add : ∀ b ∈ K, η * ∑ s ∈ range t, y s x + F x ≤ η * ∑ s ∈ range t, y s b + F b + ε

/-- A play of FTRL is a `0`-approximate play. -/
lemma IsFTRLPlay.isApproxFTRLPlay (h : IsFTRLPlay K F η y t x) : IsApproxFTRLPlay K F η y t 0 x :=
  ⟨h.mem, fun b hb ↦ by simpa using isMinOn_iff.mp h.isMinOn b hb⟩

/-- The `0`-approximate plays of FTRL are its plays. -/
lemma isApproxFTRLPlay_zero_iff : IsApproxFTRLPlay K F η y t 0 x ↔ IsFTRLPlay K F η y t x :=
  ⟨fun h ↦ ⟨h.mem, isMinOn_iff.mpr fun b hb ↦ by simpa using h.le_add b hb⟩,
    IsFTRLPlay.isApproxFTRLPlay⟩

/-- An `ε`-approximate play is `ε'`-approximate for every `ε' ≥ ε`. -/
lemma IsApproxFTRLPlay.mono (h : IsApproxFTRLPlay K F η y t ε x) (hεε' : ε ≤ ε') :
    IsApproxFTRLPlay K F η y t ε' x :=
  ⟨h.mem, fun b hb ↦ (h.le_add b hb).trans (by linarith)⟩

/-- Approximate plays exist only for a nonnegative error. -/
lemma IsApproxFTRLPlay.nonneg (h : IsApproxFTRLPlay K F η y t ε x) : 0 ≤ ε := by
  have := h.le_add x h.mem
  linarith

/-- **Existence of approximate plays.** If the objective `b ↦ η ∑ s < t, y s b + F b` of round `t`
is bounded below on a nonempty set `K`, then for every `ε > 0` there is an `ε`-approximate play
of FTRL on `K` at round `t`. No compactness is needed. -/
lemma exists_isApproxFTRLPlay (hK : K.Nonempty)
    (h_bdd : BddBelow ((fun b ↦ η * ∑ s ∈ range t, y s b + F b) '' K)) (hε : 0 < ε) :
    ∃ x, IsApproxFTRLPlay K F η y t ε x := by
  set φ := fun b ↦ η * ∑ s ∈ range t, y s b + F b
  have h_ne : (φ '' K).Nonempty := hK.image φ
  obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ :=
    exists_lt_of_csInf_lt h_ne (lt_add_of_pos_right (sInf (φ '' K)) hε)
  refine ⟨x, hx, fun b hb ↦ ?_⟩
  have := csInf_le h_bdd ⟨b, hb, rfl⟩
  simp only [φ] at hlt this
  linarith

/-- **Stability of approximate FTRL** [SSKM26, Lemma 51]. Let `K` be convex and let `F` be
`m`-strongly convex on `K`, with `m > 0`. If `x` is an `ε`-approximate play of FTRL at round `t`
and `w` is a play of FTRL at round `t + 1` where `F` has derivative `F'` within `K`, with the same
potential and learning rate `η ≥ 0`, then `‖x - w‖ ≤ 2 η ‖y t‖ / m + √(2 ε / m)`.

The paper states the case `m = 1` and `‖y t‖ ≤ 1`: `‖x - w‖ ≤ 2 η + √(2 ε)`. -/
lemma IsApproxFTRLPlay.norm_sub_le {m : ℝ} {w : E} {F' : E →L[ℝ] ℝ}
    (h : IsApproxFTRLPlay K F η y t ε x) (hw : IsFTRLPlay K F η y (t + 1) w) (hK : Convex ℝ K)
    (hF : StrongConvexOn K m F) (hm : 0 < m) (hη : 0 ≤ η) (hF' : HasFDerivWithinAt F F' K w) :
    ‖x - w‖ ≤ 2 * η * ‖y t‖ / m + √(2 * ε / m) := by
  -- `w` minimizes `c ↦ L c + F c` for the cumulative loss `L` of the rounds up to `t`, so the
  -- objective of round `t + 1` increases from `w` to `x` by at least `D_F(x, w)`
  have h_min : IsMinOn (fun c ↦ (η • ∑ s ∈ range (t + 1), y s) c + F c) K w := by
    simpa [FunLike.coe_sum, Finset.sum_apply] using hw.isMinOn
  have h_breg := bregDiv_le_sub_of_isMinOn (hK.segment_subset hw.mem h.mem) h_min hF'
  have h_sc := hF.mul_norm_sub_sq_le_bregDiv hw.mem h.mem hF'
  have h_app := h.le_add w hw.mem
  have h_y : y t (x - w) ≤ ‖y t‖ * ‖x - w‖ :=
    (le_abs_self _).trans ((y t).le_opNorm _)
  simp only [smul_apply, smul_eq_mul, sum_range_succ, add_apply, sum_apply]
    at h_breg
  -- `m / 2 ‖x - w‖² ≤ ε + η y t (x - w) ≤ η ‖y t‖ ‖x - w‖ + ε`
  have h_quad : m / 2 * ‖x - w‖ ^ 2 ≤ η * ‖y t‖ * ‖x - w‖ + ε := by
    have := mul_le_mul_of_nonneg_left h_y hη
    rw [map_sub] at this
    nlinarith
  refine (Real.le_div_add_sqrt_div_of_mul_sq_le (half_pos hm) (by positivity) h.nonneg
    h_quad).trans_eq ?_
  rw [div_div_eq_mul_div, div_div_eq_mul_div]
  ring_nf

/-- **Regret of approximate FTRL with a strongly convex potential** [SSKM26, Theorem 52]. Let `K`
be compact and convex, and let `F` have a derivative `F' z` within `K` at every `z ∈ K` and be
`m`-strongly convex on `K`, with `m > 0`. Let `η > 0`, let `a 0` be a play of FTRL at round `0`
(a minimizer of `F` over `K`), and let each `a t`, for `t < n`, be an `ε t`-approximate play of
FTRL on `K` at round `t`, with potential `F` and learning rate `η`. Then for every `u ∈ K`,
`∑ t < n, y t (a t - u) ≤ (F u - F (a 0)) / η + ∑ t < n, ‖y t‖ (2 η ‖y t‖ / m + √(2 ε t / m))`,
where `‖y t‖` is the dual norm of the loss. Each approximate play is compared with the exact play
of the next round (`IsApproxFTRLPlay.norm_sub_le`), and the exact plays satisfy the
be-the-leader inequality: the errors of the rounds do not compound.

The paper states the case `m = 1`, `‖y t‖ ≤ 1` and `ε t = ε`. -/
lemma approxFTRL_sum_apply_sub_le {m : ℝ} {n : ℕ} {u : E} (hK : Convex ℝ K) (hKc : IsCompact K)
    (F' : E → E →L[ℝ] ℝ) (hF' : ∀ z ∈ K, HasFDerivWithinAt F (F' z) K z)
    (hF : StrongConvexOn K m F) (hm : 0 < m) (hη : 0 < η) (y : ℕ → E →L[ℝ] ℝ) (ε : ℕ → ℝ)
    (a : ℕ → E) (ha0 : IsFTRLPlay K F η y 0 (a 0))
    (ha : ∀ t < n, IsApproxFTRLPlay K F η y t (ε t) (a t)) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤
      (F u - F (a 0)) / η + ∑ t ∈ range n, ‖y t‖ * (2 * η * ‖y t‖ / m + √(2 * ε t / m)) := by
  -- exact plays `x t` of every round, with `x 0 = a 0`
  obtain ⟨w, hw⟩ := exists_ftrl hKc ⟨u, hu⟩ (fun z hz ↦ (hF' z hz).continuousWithinAt) η y
  set x : ℕ → E := fun t ↦ if t = 0 then a 0 else w t with hx_def
  have hx (t : ℕ) : IsFTRLPlay K F η y t (x t) := by
    rcases eq_or_ne t 0 with rfl | ht
    · simpa [hx_def] using ha0
    · simpa [hx_def, ht] using hw t
  have hx0 : x 0 = a 0 := by simp [hx_def]
  -- the FTRL inequality for the regularizer `F / η`, with the exact plays `x` as leaders
  have h_obj (t : ℕ) : IsMinOn (fun b ↦ ∑ s ∈ range t, y s b + F b / η) K (x t) := by
    simpa using (hx t).isMinOn_sum_add_sub_div hη 0
  have h_ftrl := regret_le_ftrl (fun _ b ↦ F b / η) (fun t b ↦ y t b) x a (u := u) (n := n)
    (by linarith [isMinOn_iff.mp (h_obj n) u hu])
  rw [regret_eq_sum_apply_sub (fun t ↦ y t), hx0] at h_ftrl
  refine h_ftrl.trans ?_
  rw [← sub_div]
  refine add_le_add le_rfl (sum_le_sum fun t ht ↦ ?_)
  have ht' := mem_range.mp ht
  -- the round-`t` objective is minimized at `x t`, and `a t` is close to `x (t + 1)`
  have h_le := isMinOn_iff.mp (h_obj t) (x (t + 1)) (hx (t + 1)).mem
  have h_norm := (ha t ht').norm_sub_le (hx (t + 1)) hK hF hm hη.le
    (hF' _ (hx (t + 1)).mem)
  have h_y : y t (a t - x (t + 1)) ≤ ‖y t‖ * ‖a t - x (t + 1)‖ :=
    (le_abs_self _).trans ((y t).le_opNorm _)
  have h_mul := mul_le_mul_of_nonneg_left h_norm (norm_nonneg (y t))
  rw [sum_range_succ, map_sub] at *
  linarith

end LMLExplore.OnlineLearning
