/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.OnlineLearning.FTRL.Basic

/-!
# Approximate plays of follow the regularized leader

Follow the regularized leader on a set `K` of a real normed space `E`, with potential `F`,
learning rate `η` and linear losses `y t : E →L[ℝ] ℝ`, plays at round `t` a minimizer over `K` of
`b ↦ η ∑ s < t, y s b + F b` (`LMLExplore.OnlineLearning.IsFTRLPlay`). An **`ε`-approximate
play** is a point of `K` whose objective is at most `ε` above the objective of every point of `K`
[SSKM26, Algorithm 1]. Unlike approximate mirror descent, the objective of each round does not
depend on the previous plays, so the errors of different rounds do not compound.

## Main definitions

* `IsApproxFTRLPlay K F η y t ε x`: `x` is an `ε`-approximate play of FTRL on `K` at round `t`,
  with potential `F`, learning rate `η` and losses `y`.

## Main statements

* `isApproxFTRLPlay_zero_iff`: the `0`-approximate plays are the plays of FTRL.
* `IsApproxFTRLPlay.mono`: an `ε`-approximate play is `ε'`-approximate for `ε ≤ ε'`.
* `IsApproxFTRLPlay.nonneg`: approximate plays exist only for `ε ≥ 0`.

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

end LMLExplore.OnlineLearning
