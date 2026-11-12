/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import LMLExplore.InformationTheory.KullbackLeibler.Finite
public import LMLExplore.OnlineLearning.ExponentialWeights
public import Schlisselberg2026Hidden.ForLMLExplore.Analysis.Convex.NegEntropy
public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent

/-!
# Mirror descent with the negative entropy on the simplex: multiplicative weights

On the simplex `simplex α`, the step of mirror descent with the negative entropy `negEntropy`, from
a point `w` with positive coordinates, with learning rate `η` and the linear loss
`b ↦ ∑ a, ℓ a * b a`, is the multiplicative weights update
`a ↦ w a * exp (-η ℓ a) / ∑ b, w b * exp (-η ℓ b)`, which is `softmax (log w - η ℓ)`. The objective
of the step is the relative entropy to this update, minus `log ∑ a, w a * exp (-η ℓ a)` (the Gibbs
variational principle), which gives:

* the exact step is unique, and it is the multiplicative weights update;
* a point `x` is an `ε`-approximate step if and only if its relative entropy to the update is at
  most `ε`;
* staying at `w` is an `ε`-approximate step if and only if
  `η ∑ a, ℓ a * w a + log ∑ a, w a * exp (-η ℓ a) ≤ ε`.

From the uniform point, the exact trajectory for the losses `ℓ 0, ℓ 1, …` is the sequence of
exponential weights `softmax (-η ∑ s < t, ℓ s)`, and it is the only exact trajectory.

The derivative of the negative entropy at `w` is `∑ a, log (w a) • ContinuousLinearMap.proj a`
(`LMLExplore.hasFDerivAt_negEntropy_pi`).

## Main statements

* `LMLExplore.OnlineLearning.mul_apply_add_bregDiv_negEntropy_eq`: the objective of a step is the
  relative entropy to the multiplicative weights update, minus `log ∑ a, w a * exp (-η ℓ a)`.
* `LMLExplore.OnlineLearning.isMirrorDescentStep_negEntropy_iff`: the step of mirror descent with
  the negative entropy is the multiplicative weights update.
* `LMLExplore.OnlineLearning.isApproxMirrorDescentStep_negEntropy_iff`: the `ε`-approximate steps
  are the points whose relative entropy to the update is at most `ε`.
* `LMLExplore.OnlineLearning.isApproxMirrorDescentStep_negEntropy_self_iff`: when staying put is an
  `ε`-approximate step.
* `LMLExplore.OnlineLearning.isMirrorDescentStep_negEntropy_add_const_iff`: adding a constant to the
  loss changes no step.
* `LMLExplore.OnlineLearning.isMirrorDescentStep_negEntropy_softmax`,
  `LMLExplore.OnlineLearning.eq_softmax_of_isMirrorDescentStep_negEntropy`: the exact trajectory
  from the uniform point is exponential weights, and it is unique.
-/

@[expose] public section

open Finset Real

namespace LMLExplore.OnlineLearning

variable {α : Type*} [Fintype α] {w x b : α → ℝ} {ℓ : α → ℝ} {η ε : ℝ}

/-- The multiplicative weights update of a point `w` with positive coordinates:
`softmax (log w + v)` is `w a * exp (v a)` normalized. -/
lemma softmax_log_add_apply (hw : ∀ a, 0 < w a) (v : α → ℝ) (a : α) :
    softmax (fun a ↦ log (w a) + v a) a = w a * exp (v a) / ∑ b, w b * exp (v b) := by
  simp only [softmax_apply, exp_add, exp_log (hw _)]

/-- A multiplicative weights update of exponential weights is exponential weights:
`softmax (log (softmax v) + u) = softmax (v + u)`. -/
lemma softmax_log_softmax_add [Nonempty α] (v u : α → ℝ) :
    softmax (fun a ↦ log (softmax v a) + u a) = softmax (fun a ↦ v a + u a) := by
  have hS : 0 < ∑ b, exp (v b) := Finset.sum_pos (fun b _ ↦ exp_pos _) Finset.univ_nonempty
  have h : (fun a ↦ log (softmax v a) + u a) =
      fun a ↦ (v a + u a) + -log (∑ b, exp (v b)) := by
    funext a
    rw [softmax_apply, log_div (exp_pos _).ne' hS.ne', log_exp]
    ring
  rw [h, softmax_add_const]

/-- **The objective of a step of mirror descent with the negative entropy** (the Gibbs
variational principle): from `w ∈ simplex α` with positive coordinates, with learning rate `η` and
loss `ℓ`, the objective `η ⟨ℓ, b⟩ + D(b, w)` at `b ∈ simplex α` is the relative entropy of `b` to
the multiplicative weights update `softmax (log w - η ℓ)`, minus
`log ∑ a, w a * exp (-η ℓ a)`. -/
lemma mul_apply_add_bregDiv_negEntropy_eq (hw : w ∈ simplex α) (hpos : ∀ a, 0 < w a)
    (ℓ : α → ℝ) (η : ℝ) (hb : b ∈ simplex α) :
    η * (∑ a, ℓ a • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ) b +
        bregDiv negEntropy b w
          (∑ a, log (w a) • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ) =
      ∑ a, b a * log (b a / softmax (fun a ↦ log (w a) - η * ℓ a) a) -
        log (∑ a, w a * exp (-(η * ℓ a))) := by
  have := nonempty_of_mem_simplex hw
  have hZ : ∑ a, w a * exp (-(η * ℓ a)) ≠ 0 :=
    (Finset.sum_pos (fun a _ ↦ mul_pos (hpos a) (exp_pos _)) Finset.univ_nonempty).ne'
  have hm : softmax (fun a ↦ log (w a) - η * ℓ a) =
      fun a ↦ w a * exp (-(η * ℓ a)) / ∑ b, w b * exp (-(η * ℓ b)) := by
    funext a
    simp_rw [sub_eq_add_neg]
    exact softmax_log_add_apply hpos _ a
  have hwb : ∀ a, w a = 0 → b a = 0 := fun a h ↦ absurd h (hpos a).ne'
  rw [hm, sum_mul_log_div_mul_exp_div_eq (mem_simplex_iff.mp hb).2 hwb hZ,
    bregDiv_negEntropy_pi hb hw hwb]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, mul_neg,
    Finset.sum_neg_distrib, Finset.mul_sum]
  ring_nf
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- The value of the objective of a step of mirror descent with the negative entropy at the
multiplicative weights update is `-log ∑ a, w a * exp (-η ℓ a)`. -/
lemma mul_apply_add_bregDiv_negEntropy_softmax (hw : w ∈ simplex α) (hpos : ∀ a, 0 < w a)
    (ℓ : α → ℝ) (η : ℝ) :
    η * (∑ a, ℓ a • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ)
        (softmax fun a ↦ log (w a) - η * ℓ a) +
      bregDiv negEntropy (softmax fun a ↦ log (w a) - η * ℓ a) w
        (∑ a, log (w a) • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ) =
      -log (∑ a, w a * exp (-(η * ℓ a))) := by
  have := nonempty_of_mem_simplex hw
  rw [mul_apply_add_bregDiv_negEntropy_eq hw hpos ℓ η (softmax_mem_simplex _)]
  simp [div_self (softmax_pos _ _).ne']

/-- **The Gibbs variational principle for a step of mirror descent**: the objective of a step of
mirror descent with the negative entropy is at least `-log ∑ a, w a * exp (-η ℓ a)` on the
simplex. -/
lemma neg_log_le_mul_apply_add_bregDiv_negEntropy (hw : w ∈ simplex α) (hpos : ∀ a, 0 < w a)
    (ℓ : α → ℝ) (η : ℝ) (hb : b ∈ simplex α) :
    -log (∑ a, w a * exp (-(η * ℓ a))) ≤
      η * (∑ a, ℓ a • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ) b +
        bregDiv negEntropy b w
          (∑ a, log (w a) • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ) := by
  have := nonempty_of_mem_simplex hw
  rw [mul_apply_add_bregDiv_negEntropy_eq hw hpos ℓ η hb]
  have : 0 ≤ ∑ a, b a * log (b a / softmax (fun a ↦ log (w a) - η * ℓ a) a) :=
    sum_mul_log_div_nonneg (mem_simplex_iff.mp hb).1 (fun a ↦ (softmax_pos _ a).le)
      (fun a h ↦ absurd h (softmax_pos _ a).ne')
      (by rw [sum_softmax, (mem_simplex_iff.mp hb).2])
  linarith

/-- **Approximate steps of mirror descent with the negative entropy**: from `w ∈ simplex α` with
positive coordinates, `x` is an `ε`-approximate step if and only if `x ∈ simplex α` and the
relative entropy of `x` to the multiplicative weights update `softmax (log w - η ℓ)` is at most
`ε`. -/
lemma isApproxMirrorDescentStep_negEntropy_iff (hw : w ∈ simplex α) (hpos : ∀ a, 0 < w a) :
    IsApproxMirrorDescentStep (simplex α) negEntropy η (∑ a, ℓ a • ContinuousLinearMap.proj a) w
        (∑ a, log (w a) • ContinuousLinearMap.proj a) ε x ↔
      x ∈ simplex α ∧ ∑ a, x a * log (x a / softmax (fun a ↦ log (w a) - η * ℓ a) a) ≤ ε := by
  have := nonempty_of_mem_simplex hw
  constructor
  · intro h
    refine ⟨h.mem, ?_⟩
    have h1 := h.le_add _ (softmax_mem_simplex (fun a ↦ log (w a) - η * ℓ a))
    rw [mul_apply_add_bregDiv_negEntropy_eq hw hpos ℓ η h.mem,
      mul_apply_add_bregDiv_negEntropy_softmax hw hpos ℓ η] at h1
    linarith
  · rintro ⟨hx, hle⟩
    refine ⟨hx, fun b hb ↦ ?_⟩
    rw [mul_apply_add_bregDiv_negEntropy_eq hw hpos ℓ η hx]
    linarith [neg_log_le_mul_apply_add_bregDiv_negEntropy hw hpos ℓ η hb]

/-- **Mirror descent with the negative entropy is multiplicative weights**: from `w ∈ simplex α`
with positive coordinates, the step of mirror descent on the simplex with the negative entropy,
learning rate `η` and loss `ℓ` is unique, and it is `softmax (log w - η ℓ)`, the point
`a ↦ w a * exp (-η ℓ a)` normalized. -/
lemma isMirrorDescentStep_negEntropy_iff (hw : w ∈ simplex α) (hpos : ∀ a, 0 < w a) :
    IsMirrorDescentStep (simplex α) negEntropy η (∑ a, ℓ a • ContinuousLinearMap.proj a) w
        (∑ a, log (w a) • ContinuousLinearMap.proj a) x ↔
      x = softmax (fun a ↦ log (w a) - η * ℓ a) := by
  have := nonempty_of_mem_simplex hw
  rw [← isApproxMirrorDescentStep_zero_iff, isApproxMirrorDescentStep_negEntropy_iff hw hpos]
  constructor
  · rintro ⟨hx, hle⟩
    have h0 : 0 ≤ ∑ a, x a * log (x a / softmax (fun a ↦ log (w a) - η * ℓ a) a) :=
      sum_mul_log_div_nonneg (mem_simplex_iff.mp hx).1 (fun a ↦ (softmax_pos _ a).le)
        (fun a h ↦ absurd h (softmax_pos _ a).ne')
        (by rw [sum_softmax, (mem_simplex_iff.mp hx).2])
    exact (sum_mul_log_div_eq_zero_iff hx (softmax_mem_simplex _)
      (fun a h ↦ absurd h (softmax_pos _ a).ne')).mp (le_antisymm hle h0)
  · rintro rfl
    exact ⟨softmax_mem_simplex _, by simp [div_self (softmax_pos _ _).ne']⟩

/-- The multiplicative weights update `softmax (log w - η ℓ)` is the step of mirror descent with
the negative entropy from a point `w` of the simplex with positive coordinates. -/
lemma isMirrorDescentStep_negEntropy (hw : w ∈ simplex α) (hpos : ∀ a, 0 < w a)
    (ℓ : α → ℝ) (η : ℝ) :
    IsMirrorDescentStep (simplex α) negEntropy η (∑ a, ℓ a • ContinuousLinearMap.proj a) w
      (∑ a, log (w a) • ContinuousLinearMap.proj a) (softmax fun a ↦ log (w a) - η * ℓ a) :=
  (isMirrorDescentStep_negEntropy_iff hw hpos).mpr rfl

/-- Adding a constant to the loss changes no step of mirror descent with the negative entropy on
the simplex. -/
lemma isMirrorDescentStep_negEntropy_add_const_iff (hw : w ∈ simplex α) (hpos : ∀ a, 0 < w a)
    (c : ℝ) :
    IsMirrorDescentStep (simplex α) negEntropy η
        (∑ a, (ℓ a + c) • ContinuousLinearMap.proj a) w
        (∑ a, log (w a) • ContinuousLinearMap.proj a) x ↔
      IsMirrorDescentStep (simplex α) negEntropy η (∑ a, ℓ a • ContinuousLinearMap.proj a) w
        (∑ a, log (w a) • ContinuousLinearMap.proj a) x := by
  rw [isMirrorDescentStep_negEntropy_iff (ℓ := fun a ↦ ℓ a + c) hw hpos,
    isMirrorDescentStep_negEntropy_iff hw hpos]
  have h : (fun a ↦ log (w a) - η * (ℓ a + c)) = fun a ↦ (log (w a) - η * ℓ a) + -(η * c) := by
    funext a
    ring
  rw [h, softmax_add_const]

/-- **Staying put with the negative entropy**: from `w ∈ simplex α` with positive coordinates,
`w` itself is an `ε`-approximate step of mirror descent if and only if
`η ⟨ℓ, w⟩ + log ∑ a, w a * exp (-η ℓ a) ≤ ε`. -/
lemma isApproxMirrorDescentStep_negEntropy_self_iff (hw : w ∈ simplex α) (hpos : ∀ a, 0 < w a) :
    IsApproxMirrorDescentStep (simplex α) negEntropy η (∑ a, ℓ a • ContinuousLinearMap.proj a) w
        (∑ a, log (w a) • ContinuousLinearMap.proj a) ε w ↔
      η * ∑ a, ℓ a * w a + log (∑ a, w a * exp (-(η * ℓ a))) ≤ ε := by
  rw [isApproxMirrorDescentStep_negEntropy_iff hw hpos]
  have h := mul_apply_add_bregDiv_negEntropy_eq hw hpos ℓ η hw
  simp only [bregDiv, sub_self, map_zero, add_zero, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul] at h
  constructor
  · rintro ⟨-, hle⟩
    linarith
  · intro hle
    exact ⟨hw, by linarith⟩

/-- **Exponential weights are the exact trajectory of mirror descent with the negative entropy**:
the step of round `t` from `softmax (-η ∑ s < t, ℓ s)`, with the loss `ℓ t`, is
`softmax (-η ∑ s < t + 1, ℓ s)`. -/
lemma isMirrorDescentStep_negEntropy_softmax [Nonempty α] (ℓ : ℕ → α → ℝ) (η : ℝ) (t : ℕ) :
    IsMirrorDescentStep (simplex α) negEntropy η (∑ a, ℓ t a • ContinuousLinearMap.proj a)
      (softmax fun a ↦ -(η * ∑ s ∈ range t, ℓ s a))
      (∑ a, log (softmax (fun a ↦ -(η * ∑ s ∈ range t, ℓ s a)) a) • ContinuousLinearMap.proj a)
      (softmax fun a ↦ -(η * ∑ s ∈ range (t + 1), ℓ s a)) := by
  rw [isMirrorDescentStep_negEntropy_iff (softmax_mem_simplex _) (softmax_pos _)]
  simp_rw [sub_eq_add_neg, softmax_log_softmax_add, Finset.sum_range_succ]
  congr 1
  funext a
  ring

/-- **The exact trajectory of mirror descent with the negative entropy is unique**: a trajectory
started at the uniform point whose terms are exact steps of mirror descent on the simplex with the
negative entropy is exponential weights, `b t = softmax (-η ∑ s < t, ℓ s)`. -/
lemma eq_softmax_of_isMirrorDescentStep_negEntropy [Nonempty α] {ℓ : ℕ → α → ℝ}
    {b : ℕ → α → ℝ} {T : ℕ} (h0 : b 0 = fun _ ↦ (Fintype.card α : ℝ)⁻¹)
    (hstep : ∀ t < T, IsMirrorDescentStep (simplex α) negEntropy η
      (∑ a, ℓ t a • ContinuousLinearMap.proj a) (b t)
      (∑ a, log (b t a) • ContinuousLinearMap.proj a) (b (t + 1))) :
    ∀ t ≤ T, b t = softmax fun a ↦ -(η * ∑ s ∈ range t, ℓ s a) := by
  intro t ht
  induction t with
  | zero =>
    rw [h0, ← softmax_zero]
    congr 1
    funext a
    simp
  | succ t ih =>
    have h := hstep t (by omega)
    rw [ih (by omega)] at h
    exact (isMirrorDescentStep_negEntropy_iff (softmax_mem_simplex _) (softmax_pos _)).mp h ▸
      ((isMirrorDescentStep_negEntropy_iff (softmax_mem_simplex _) (softmax_pos _)).mp
        (isMirrorDescentStep_negEntropy_softmax ℓ η t)).symm

end LMLExplore.OnlineLearning
