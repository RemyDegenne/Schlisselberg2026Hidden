/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.OnlineLearning.MirrorDescent

/-!
# Approximate mirror descent steps

Online linear optimization on a set `K` of a real normed space `E`, with losses `y t : E →L[ℝ] ℝ`,
as in `LMLExplore.OnlineLearning.MirrorDescent`. A step of mirror descent from `a` with potential
`F`, derivative `F'` of `F` at `a`, learning rate `η` and loss `y` minimizes over `K` the
objective `b ↦ η y b + D_F(b, a)`, where `D_F(b, a) = F b - F a - F'(b - a)` is the Bregman
divergence. In practice this subproblem is often solved only approximately: an
**`ε`-approximate step** is a point of `K` whose objective is at most `ε` above the objective of
every point of `K` [SSKM26, Section 2]. The infimum of the objective need not be attained. For
`ε = 0` these are the steps of `LMLExplore.OnlineLearning.IsMirrorDescentStep`.

A sequence `a` with `a 0 ∈ K` whose terms `a (t + 1)` are `ε`-approximate steps from `a t` for the
losses `y t` is an `ε`-approximate trajectory of online mirror descent [SSKM26, Section 2,
Definition 17].

## Main definitions

* `IsApproxMirrorDescentStep K F η y a F' ε x`: `x` is an `ε`-approximate step of mirror descent
  on `K` from `a`, with potential `F`, derivative `F'` of `F` at `a`, learning rate `η` and loss
  `y`.

## Main statements

* `isApproxMirrorDescentStep_zero_iff`: the `0`-approximate steps are the mirror descent steps.
* `IsApproxMirrorDescentStep.mono`: an `ε`-approximate step is `ε'`-approximate for `ε ≤ ε'`.
* `IsApproxMirrorDescentStep.nonneg`: approximate steps exist only for `ε ≥ 0`.
* `exists_isApproxMirrorDescentStep`: if the objective is bounded below on a nonempty `K`, then
  `ε`-approximate steps exist for every `ε > 0`.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

namespace LMLExplore.OnlineLearning

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {F : E → ℝ} {η : ℝ}
  {y F' : E →L[ℝ] ℝ} {a x : E} {ε ε' : ℝ}

/-- `x` is an **`ε`-approximate mirror descent step** [SSKM26, Section 2] on `K` from `a`, with
potential `F`, linear map `F'`, learning rate `η` and loss `y`: `x ∈ K`, and the objective
`b ↦ η y b + D_F(b, a)` at `x` is at most `ε` above its value at every point of `K`, where
`D_F(b, a) = F b - F a - F' (b - a)` is the Bregman divergence. `F'` is intended to be a
derivative of `F` at `a`, but the predicate does not require it. -/
structure IsApproxMirrorDescentStep (K : Set E) (F : E → ℝ) (η : ℝ) (y : E →L[ℝ] ℝ) (a : E)
    (F' : E →L[ℝ] ℝ) (ε : ℝ) (x : E) : Prop where
  /-- The step lies in `K`. -/
  mem : x ∈ K
  /-- The objective at the step is at most `ε` above its value at every point of `K`. -/
  le_add : ∀ b ∈ K, η * y x + bregDiv F x a F' ≤ η * y b + bregDiv F b a F' + ε

/-- A mirror descent step is a `0`-approximate step. -/
lemma IsMirrorDescentStep.isApproxMirrorDescentStep (h : IsMirrorDescentStep K F η y a F' x) :
    IsApproxMirrorDescentStep K F η y a F' 0 x :=
  ⟨h.mem, fun b hb ↦ by simpa using isMinOn_iff.mp h.isMinOn b hb⟩

/-- The `0`-approximate steps of mirror descent are its steps. -/
lemma isApproxMirrorDescentStep_zero_iff :
    IsApproxMirrorDescentStep K F η y a F' 0 x ↔ IsMirrorDescentStep K F η y a F' x :=
  ⟨fun h ↦ ⟨h.mem, isMinOn_iff.mpr fun b hb ↦ by simpa using h.le_add b hb⟩,
    IsMirrorDescentStep.isApproxMirrorDescentStep⟩

/-- An `ε`-approximate step is `ε'`-approximate for every `ε' ≥ ε`. -/
lemma IsApproxMirrorDescentStep.mono (h : IsApproxMirrorDescentStep K F η y a F' ε x)
    (hεε' : ε ≤ ε') : IsApproxMirrorDescentStep K F η y a F' ε' x :=
  ⟨h.mem, fun b hb ↦ (h.le_add b hb).trans (by linarith)⟩

/-- Approximate steps exist only for a nonnegative error. -/
lemma IsApproxMirrorDescentStep.nonneg (h : IsApproxMirrorDescentStep K F η y a F' ε x) :
    0 ≤ ε := by
  have := h.le_add x h.mem
  linarith

/-- **Existence of approximate steps.** If the objective `b ↦ η y b + D_F(b, a)` of a mirror
descent step is bounded below on a nonempty set `K`, then for every `ε > 0` there is an
`ε`-approximate step on `K` from `a`. No compactness is needed. -/
lemma exists_isApproxMirrorDescentStep (hK : K.Nonempty)
    (h_bdd : BddBelow ((fun b ↦ η * y b + bregDiv F b a F') '' K)) (hε : 0 < ε) :
    ∃ x, IsApproxMirrorDescentStep K F η y a F' ε x := by
  set φ := fun b ↦ η * y b + bregDiv F b a F'
  have h_ne : (φ '' K).Nonempty := hK.image φ
  obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ :=
    exists_lt_of_csInf_lt h_ne (lt_add_of_pos_right (sInf (φ '' K)) hε)
  refine ⟨x, hx, fun b hb ↦ ?_⟩
  have := csInf_le h_bdd ⟨b, hb, rfl⟩
  simp only [φ] at hlt this
  linarith

end LMLExplore.OnlineLearning
