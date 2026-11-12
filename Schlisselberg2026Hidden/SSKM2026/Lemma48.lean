/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.SSKM2026.Lemma44
public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Lemma 48 of [SSKM26]: the steps of the trajectory of Theorem 8

On the polytope `K_m` of `Schlisselberg2026Hidden.SSKM2026.Lemma44`, with `d = 5 m + 2`, the
trajectory of Theorem 8 of [SSKM26] stays on a curve: for `E > 0` and `q ∈ (0, 2 / d)`, the point
`W(E, q)` has `y = (3 / d + q) / (E + 3)` on the `Y`-coordinates, `E y` on the `X`-coordinates,
`2 / d - q` on the `Z`-coordinates and on `P`, and `q` on `Q`. After `n` rounds, `E = e^{η n}`.

For a loss `ℓ` of the construction (`0` on `X` and `Q`, `1` on `Y`) with
`S(ℓ) = ∑ i, ℓ (Z i) + ℓ P`, the objective of a step from `W(E, q)` compared at `W(e^η E, q')` and
at a point `b` of `K_m` differs by `r (b Q - q')` plus a nonnegative divergence, where
`r = f(e^η E, q') - f(E, q) - η S(ℓ)` and `f(E, q) = m log (E y) + log q - (m + 1) log (2 / d - q)`
(`PolytopeLower.level`). Hence (`PolytopeLower.isApproxMirrorDescentStep_curve`):
* the **exact step** from `W(E, q)` is `W(e^η E, q')` with `f(e^η E, q') = f(E, q) + η S(ℓ)`;
* the **frozen step** `W(e^η E, q)` is `q h(r)`-approximate, with `h(r) = e^{-r} - 1 + r`.

This replaces the paper's Lemma 48, whose proof that its modified step is approximate has gaps
(`notes/paper-errata.md`, E33). The trajectory of Theorem 8 (`PolytopeLower.traj`) takes exact
steps for `τ` rounds, then frozen steps as long as they are `ε`-approximate, exact steps
otherwise; it is an `ε`-approximate trajectory for every loss sequence of the construction, and
each play is a measurable function of the past losses.

## Main definitions

* `PolytopeLower.curve m E q`: the point `W(E, q)`.
* `PolytopeLower.level m E q`: the function `f(E, q)`, strictly increasing from `(0, 2 / d)` onto
  `ℝ`, with inverse `PolytopeLower.levelInv m E`.
* `PolytopeLower.traj m η ε τ n ℓ`: the play of round `n` of the trajectory, for the losses `ℓ`.

## Main statements

* `PolytopeLower.isApproxMirrorDescentStep_curve`: [SSKM26, Lemma 48], corrected: the steps along
  the curve and their errors.
* `PolytopeLower.isApproxMirrorDescentStep_traj`: the trajectory is `ε`-approximate.
* `PolytopeLower.measurable_traj`, `PolytopeLower.traj_congr`: each play is a measurable function
  of the losses of the past rounds.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Real Set

namespace Schlisselberg2026Hidden.PolytopeLower

variable {m : ℕ}

/-! ### The objective of a step on `α → ℝ` -/

section Objective

variable {ι : Type*} [Fintype ι]

/-- **The gap of the objective of a step** of mirror descent with the negative entropy on
`ι → ℝ`, in three-point form [SSKM26, Lemma 26]: for the objective
`φ(b) = η ⟨ℓ, b⟩ + D(b, a)`, `φ(b) - φ(x)` is `⟨η ℓ + log x - log a, b - x⟩` plus the sum over
the coordinates of `b log b - b log x - b + x`. Pure algebra: no positivity is needed. -/
lemma objective_sub_objective (η : ℝ) (ℓ a x b : ι → ℝ) :
    (η * (∑ j, ℓ j • ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ) b +
        bregDiv negEntropy b a
          (∑ j, log (a j) • ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ)) -
      (η * (∑ j, ℓ j • ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ) x +
        bregDiv negEntropy x a
          (∑ j, log (a j) • ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ)) =
    ∑ j, (η * ℓ j + log (x j) - log (a j)) * (b j - x j) +
      ∑ j, (b j * log (b j) - b j * log (x j) - b j + x j) := by
  simp only [bregDiv, negEntropy_def, sum_smul_proj_apply, Pi.sub_apply, Finset.mul_sum]
  rw [← sub_eq_zero]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun j _ ↦ by ring

/-- The scalar Bregman divergence of `x log x - x`: `s log s - s log c - s + c ≥ 0` for `s ≥ 0`
and `c > 0`. -/
lemma entropyGap_nonneg {s c : ℝ} (hs : 0 ≤ s) (hc : 0 < c) :
    0 ≤ s * log s - s * log c - s + c := by
  rcases hs.eq_or_lt with rfl | hs
  · simpa using hc.le
  have h := one_sub_inv_le_log_of_pos (div_pos hs hc)
  rw [log_div hs.ne' hc.ne', inv_div] at h
  have : s * (1 - c / s) ≤ s * (log s - log c) := mul_le_mul_of_nonneg_left h hs.le
  rw [mul_sub, mul_one, mul_div_cancel₀ _ hs.ne'] at this
  linarith

/-- The function `h(r) = e^{-r} - 1 + r ≥ 0` of the error of the frozen step. -/
noncomputable def expRem (r : ℝ) : ℝ := exp (-r) - 1 + r

lemma expRem_nonneg (r : ℝ) : 0 ≤ expRem r := by
  have := add_one_le_exp (-r)
  rw [expRem]
  linarith

@[simp] lemma expRem_zero : expRem 0 = 0 := by simp [expRem]

/-- `h(r) ≤ 3` for `|r| ≤ 1`. -/
lemma expRem_le_three {r : ℝ} (hr : |r| ≤ 1) : expRem r ≤ 3 := by
  have h1 : exp (-r) ≤ exp 1 := exp_le_exp.mpr (by linarith [neg_abs_le r, le_abs_self r])
  have h2 := exp_one_lt_d9
  have h3 := le_abs_self r
  rw [expRem]
  linarith

lemma measurable_expRem : Measurable expRem := by
  unfold expRem
  fun_prop

/-- **The one-dimensional conjugate bound** [SSKM26, proof of Lemma 48], corrected:
`r (s - c) + (s log s - s log c - s + c) ≥ -c h(r)` for `s ≥ 0` and `c > 0`. -/
lemma neg_mul_expRem_le {s c : ℝ} (r : ℝ) (hs : 0 ≤ s) (hc : 0 < c) :
    -(c * expRem r) ≤ r * (s - c) + (s * log s - s * log c - s + c) := by
  have h := entropyGap_nonneg hs (mul_pos hc (exp_pos (-r)))
  rw [log_mul hc.ne' (exp_pos _).ne', log_exp] at h
  rw [expRem]
  nlinarith

end Objective

/-! ### The curve -/

/-- The `Y`-coordinate `(3 / d + q) / (E + 3)` of the point `W(E, q)` of the curve. -/
noncomputable def curveY (m : ℕ) (E q : ℝ) : ℝ := (3 / (5 * m + 2) + q) / (E + 3)

/-- The point `W(E, q)` of the curve of the trajectory of Theorem 8 of [SSKM26]: `E y` on the
`X`-coordinates, `y = curveY m E q` on the `Y`-coordinates, `2 / d - q` on the `Z`-coordinates
and on `P`, and `q` on `Q`. -/
noncomputable def curve (m : ℕ) (E q : ℝ) : Fin m × Fin 5 ⊕ Fin 2 → ℝ :=
  Sum.elim (fun p ↦ ![E * curveY m E q, curveY m E q, curveY m E q, curveY m E q,
    2 / (5 * m + 2) - q] p.2) ![2 / (5 * m + 2) - q, q]

section Curve

variable {E q : ℝ} (i : Fin m)

@[simp] lemma curve_X : curve m E q (.inl (i, 0)) = E * curveY m E q := rfl
@[simp] lemma curve_Y1 : curve m E q (.inl (i, 1)) = curveY m E q := rfl
@[simp] lemma curve_Y2 : curve m E q (.inl (i, 2)) = curveY m E q := rfl
@[simp] lemma curve_Y3 : curve m E q (.inl (i, 3)) = curveY m E q := rfl
@[simp] lemma curve_Z : curve m E q (.inl (i, 4)) = 2 / (5 * m + 2) - q := rfl
@[simp] lemma curve_P : curve m E q (.inr 0) = 2 / (5 * m + 2) - q := rfl
@[simp] lemma curve_Q : curve m E q (.inr 1) = q := rfl

variable {i}

lemma curveY_pos (hE : 0 < E) (hq : 0 < q) : 0 < curveY m E q := by
  unfold curveY
  positivity

lemma add_three_mul_curveY (hE : 0 < E) :
    E * curveY m E q + 3 * curveY m E q = 3 / (5 * m + 2) + q := by
  unfold curveY
  field_simp

/-- The points of the curve have positive coordinates. -/
lemma curve_pos (hE : 0 < E) (hq : q ∈ Ioo 0 (2 / (5 * m + 2) : ℝ)) (j : Fin m × Fin 5 ⊕ Fin 2) :
    0 < curve m E q j := by
  have hy := curveY_pos (m := m) hE hq.1
  have hz : 0 < 2 / (5 * m + 2 : ℝ) - q := by linarith [hq.2]
  rcases j with ⟨i, k⟩ | k
  · fin_cases k
    exacts [mul_pos hE hy, hy, hy, hy, hz]
  · fin_cases k
    exacts [hz, hq.1]

/-- The curve lies in the polytope. -/
lemma curve_mem_polytope (hE : 0 < E) (hq : q ∈ Ioo 0 (2 / (5 * m + 2) : ℝ)) :
    curve m E q ∈ polytope m := by
  refine ⟨fun j ↦ (curve_pos hE hq j).le, fun i ↦ ⟨rfl, rfl, rfl, ?_⟩, by simp⟩
  simp only [curve_X, curve_Y1, curve_Z]
  linear_combination add_three_mul_curveY (m := m) (q := q) hE

variable (m) in
/-- The curve is continuous in `q`. -/
lemma continuous_curve (E : ℝ) : Continuous (curve m E) := by
  refine continuous_pi fun j ↦ ?_
  match j with
  | .inl (i, 0) => simp only [curve_X]; unfold curveY; fun_prop
  | .inl (i, 1) => simp only [curve_Y1]; unfold curveY; fun_prop
  | .inl (i, 2) => simp only [curve_Y2]; unfold curveY; fun_prop
  | .inl (i, 3) => simp only [curve_Y3]; unfold curveY; fun_prop
  | .inl (i, 4) => simp only [curve_Z]; fun_prop
  | .inr 0 => simp only [curve_P]; fun_prop
  | .inr 1 => simp only [curve_Q]; fun_prop

/-- The start of the curve is the uniform point. -/
lemma curve_one_inv : curve m 1 (5 * m + 2 : ℝ)⁻¹ = fun _ ↦ (5 * m + 2 : ℝ)⁻¹ := by
  have hd : (0 : ℝ) < 5 * m + 2 := by positivity
  have hy : curveY m 1 (5 * m + 2 : ℝ)⁻¹ = (5 * m + 2 : ℝ)⁻¹ := by
    unfold curveY
    field_simp
    ring
  have hz : 2 / (5 * m + 2 : ℝ) - (5 * m + 2 : ℝ)⁻¹ = (5 * m + 2 : ℝ)⁻¹ := by
    field_simp
    ring
  ext j
  rcases j with ⟨i, k⟩ | k
  · fin_cases k <;> simp [hy, hz]
  · fin_cases k <;> simp [hz]

end Curve

/-! ### The level function -/

/-- The function `f(E, q) = m log (E y) + log q - (m + 1) log (2 / d - q)` that the exact steps
move by `η S(ℓ)`, with `y = curveY m E q`. -/
noncomputable def level (m : ℕ) (E q : ℝ) : ℝ :=
  m * log (E * curveY m E q) + log q - (m + 1) * log (2 / (5 * m + 2) - q)

section Level

variable {E q : ℝ}

lemma measurable_level (m : ℕ) (E : ℝ) : Measurable (level m E) := by
  unfold level curveY
  fun_prop

lemma continuousOn_level (hE : 0 < E) :
    ContinuousOn (level m E) (Ioo 0 (2 / (5 * m + 2))) := by
  have h1 : ContinuousOn (fun q ↦ log (E * curveY m E q)) (Ioo 0 (2 / (5 * m + 2))) :=
    ContinuousOn.log (by unfold curveY; fun_prop) fun q hq ↦ (mul_pos hE (curveY_pos hE hq.1)).ne'
  have h2 : ContinuousOn log (Ioo 0 (2 / (5 * m + 2) : ℝ)) :=
    continuousOn_log.mono fun q hq ↦ hq.1.ne'
  have h3 : ContinuousOn (fun q ↦ log (2 / (5 * m + 2) - q)) (Ioo 0 (2 / (5 * m + 2))) :=
    ContinuousOn.log (by fun_prop) fun q hq ↦ (sub_pos.mpr hq.2).ne'
  exact ((continuousOn_const.mul h1).add h2).sub (continuousOn_const.mul h3)

lemma curveY_le_curveY {q q' : ℝ} (hE : 0 < E) (h : q ≤ q') : curveY m E q ≤ curveY m E q' := by
  unfold curveY
  gcongr

/-- The level function is strictly increasing on `(0, 2 / d)`. -/
lemma strictMonoOn_level (hE : 0 < E) : StrictMonoOn (level m E) (Ioo 0 (2 / (5 * m + 2))) := by
  intro q hq q' hq' hqq'
  have h1 : log (E * curveY m E q) ≤ log (E * curveY m E q') :=
    log_le_log (mul_pos hE (curveY_pos hE hq.1)) (by gcongr; exact curveY_le_curveY hE hqq'.le)
  have h2 : log q < log q' := log_lt_log hq.1 hqq'
  have h3 : log (2 / (5 * m + 2) - q') ≤ log (2 / (5 * m + 2) - q) :=
    log_le_log (sub_pos.mpr hq'.2) (by linarith)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold level
  nlinarith

/-- The part `m log (E y) - m log (2 / d - q)` of the level function, monotone in `q`. -/
lemma level_eq (E q : ℝ) :
    level m E q = (m * log (E * curveY m E q) - m * log (2 / (5 * m + 2) - q)) + log q -
      log (2 / (5 * m + 2) - q) := by
  unfold level
  ring

lemma monotoneOn_level_aux (hE : 0 < E) :
    MonotoneOn (fun q ↦ m * log (E * curveY m E q) - m * log (2 / (5 * m + 2) - q))
      (Ioo 0 (2 / (5 * m + 2))) := by
  intro q hq q' hq' hqq'
  have h1 : log (E * curveY m E q) ≤ log (E * curveY m E q') :=
    log_le_log (mul_pos hE (curveY_pos hE hq.1)) (by gcongr; exact curveY_le_curveY hE hqq')
  have h3 : log (2 / (5 * m + 2) - q') ≤ log (2 / (5 * m + 2) - q) :=
    log_le_log (sub_pos.mpr hq'.2) (by linarith)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  simp only
  nlinarith

/-- **The level function is onto `ℝ`** from `(0, 2 / d)`. -/
lemma exists_level_eq (hE : 0 < E) (γ : ℝ) :
    ∃ q ∈ Ioo 0 (2 / (5 * m + 2) : ℝ), level m E q = γ := by
  set d : ℝ := 5 * m + 2 with hd_def
  have hd : 0 < d := by positivity
  set A : ℝ → ℝ := fun q ↦ m * log (E * curveY m E q) - m * log (2 / d - q) with hA
  have hmid : d⁻¹ ∈ Ioo 0 (2 / d) :=
    ⟨by positivity, by rw [div_eq_mul_inv]; linarith [inv_pos.mpr hd]⟩
  set A₀ := A d⁻¹
  set c₁ := min 1 (exp (γ - A₀))
  set c₂ := min 1 (exp (A₀ - γ))
  have hc₁ : 0 < c₁ := lt_min one_pos (exp_pos _)
  have hc₂ : 0 < c₂ := lt_min one_pos (exp_pos _)
  set q₁ := d⁻¹ * c₁
  set q₂ := 2 / d - d⁻¹ * c₂
  have hq₁ : q₁ ∈ Ioo 0 (2 / d) := ⟨by positivity, by
    have : q₁ ≤ d⁻¹ := mul_le_of_le_one_right (inv_pos.mpr hd).le (min_le_left _ _)
    linarith [hmid.2]⟩
  have hq₁' : q₁ ≤ d⁻¹ := mul_le_of_le_one_right (inv_pos.mpr hd).le (min_le_left _ _)
  have hq₂' : d⁻¹ ≤ q₂ := by
    have : d⁻¹ * c₂ ≤ d⁻¹ := mul_le_of_le_one_right (inv_pos.mpr hd).le (min_le_left _ _)
    have : 2 / d = 2 * d⁻¹ := by ring
    linarith
  have hq₂ : q₂ ∈ Ioo 0 (2 / d) := ⟨by linarith [hmid.1], by
    have : 0 < d⁻¹ * c₂ := by positivity
    linarith⟩
  have hmono := monotoneOn_level_aux (m := m) hE
  -- `f(q₁) ≤ γ`
  have hf₁ : level m E q₁ ≤ γ := by
    rw [level_eq]
    have hA₁ : A q₁ ≤ A₀ := hmono hq₁ hmid hq₁'
    have hlog₁ : log q₁ ≤ log d⁻¹ + (γ - A₀) := by
      rw [log_mul (inv_pos.mpr hd).ne' hc₁.ne']
      have : log c₁ ≤ γ - A₀ := by
        calc log c₁ ≤ log (exp (γ - A₀)) := log_le_log hc₁ (min_le_right _ _)
          _ = γ - A₀ := log_exp _
      linarith
    have hlog₂ : log d⁻¹ ≤ log (2 / d - q₁) :=
      log_le_log (inv_pos.mpr hd) (by rw [div_eq_mul_inv]; linarith)
    simp only [hA] at hA₁
    linarith
  -- `γ ≤ f(q₂)`
  have hf₂ : γ ≤ level m E q₂ := by
    rw [level_eq]
    have hA₂ : A₀ ≤ A q₂ := hmono hmid hq₂ hq₂'
    have hz : 2 / d - q₂ = d⁻¹ * c₂ := by ring
    have hlog₁ : log (2 / d - q₂) ≤ log d⁻¹ + (A₀ - γ) := by
      rw [hz, log_mul (inv_pos.mpr hd).ne' hc₂.ne']
      have : log c₂ ≤ A₀ - γ := by
        calc log c₂ ≤ log (exp (A₀ - γ)) := log_le_log hc₂ (min_le_right _ _)
          _ = A₀ - γ := log_exp _
      linarith
    have hlog₂ : log d⁻¹ ≤ log q₂ := log_le_log (inv_pos.mpr hd) hq₂'
    simp only [hA] at hA₂
    linarith
  have hsub : Icc q₁ q₂ ⊆ Ioo 0 (2 / d) := fun q hq ↦ ⟨hq₁.1.trans_le hq.1, hq.2.trans_lt hq₂.2⟩
  obtain ⟨q, hq, hfq⟩ :=
    intermediate_value_Icc (hq₁'.trans hq₂') ((continuousOn_level hE).mono hsub) ⟨hf₁, hf₂⟩
  exact ⟨q, hsub hq, hfq⟩

/-- The inverse of the level function, from `ℝ` onto `(0, 2 / d)`. -/
noncomputable def levelInv (m : ℕ) (E γ : ℝ) : ℝ :=
  Function.invFunOn (level m E) (Ioo 0 (2 / (5 * m + 2))) γ

lemma levelInv_mem (hE : 0 < E) (γ : ℝ) : levelInv m E γ ∈ Ioo 0 (2 / (5 * m + 2) : ℝ) :=
  (Function.invFunOn_pos (exists_level_eq hE γ)).1

lemma level_levelInv (hE : 0 < E) (γ : ℝ) : level m E (levelInv m E γ) = γ :=
  (Function.invFunOn_pos (exists_level_eq hE γ)).2

lemma levelInv_level (hE : 0 < E) (hq : q ∈ Ioo 0 (2 / (5 * m + 2) : ℝ)) :
    levelInv m E (level m E q) = q :=
  (strictMonoOn_level hE).injOn (levelInv_mem hE _) hq (level_levelInv hE _)

lemma monotone_levelInv (hE : 0 < E) : Monotone (levelInv m E) := by
  intro γ γ' h
  by_contra! hlt
  have := (strictMonoOn_level hE) (levelInv_mem hE γ') (levelInv_mem hE γ) hlt
  rw [level_levelInv hE, level_levelInv hE] at this
  linarith

lemma measurable_levelInv (hE : 0 < E) : Measurable (levelInv m E) :=
  (monotone_levelInv hE).measurable

end Level

/-! ### Steps along the curve -/

/-- The paper's `S(ℓ) = ∑ i, ℓ (Z i) + ℓ P`, the part of the loss that moves the trajectory. -/
def lossZP (x : Fin m × Fin 5 ⊕ Fin 2 → ℝ) : ℝ := ∑ i, x (.inl (i, 4)) + x (.inr 0)

lemma measurable_lossZP : Measurable (lossZP (m := m)) := by
  unfold lossZP
  fun_prop

/-- **The residual of a step along the curve** [SSKM26, proof of Lemma 48], corrected: for a loss
of the construction and `b` in the polytope, the linear part of the gap between the objectives
at `b` and at `W(e^η E, q')`, for the step from `W(E, q)`, is
`(f(e^η E, q') - f(E, q) - η S(ℓ)) (b Q - q')`. -/
lemma sum_mul_sub_curve {η E E' q q' : ℝ} {ℓ b : Fin m × Fin 5 ⊕ Fin 2 → ℝ} (hE : 0 < E)
    (hE' : E' = exp η * E) (hq : q ∈ Ioo 0 (2 / (5 * m + 2) : ℝ))
    (hq' : q' ∈ Ioo 0 (2 / (5 * m + 2) : ℝ)) (hℓ : IsShapedLoss ℓ) (hb : b ∈ polytope m) :
    ∑ j, (η * ℓ j + log (curve m E' q' j) - log (curve m E q j)) * (b j - curve m E' q' j) =
      (level m E' q' - level m E q - η * lossZP ℓ) * (b (.inr 1) - q') := by
  have hE'pos : 0 < E' := hE' ▸ mul_pos (exp_pos η) hE
  set y := curveY m E q
  set y' := curveY m E' q'
  set z := 2 / (5 * m + 2 : ℝ) - q
  set z' := 2 / (5 * m + 2 : ℝ) - q'
  have hy : 0 < y := curveY_pos hE hq.1
  have hy' : 0 < y' := curveY_pos hE'pos hq'.1
  have hA : log (E' * y') = η + log E + log y' := by
    rw [hE', log_mul (mul_pos (exp_pos η) hE).ne' hy'.ne', log_mul (exp_pos η).ne' hE.ne', log_exp]
  have hB : log (E * y) = log E + log y := log_mul hE.ne' hy.ne'
  have hyy : E' * y' + 3 * y' = 3 / (5 * m + 2) + q' := add_three_mul_curveY hE'pos
  set gX := η + log y' - log y
  have hterm : ∀ i : Fin m,
      (η * ℓ (.inl (i, 0)) + log (E' * y') - log (E * y)) * (b (.inl (i, 0)) - E' * y') +
        (η * ℓ (.inl (i, 1)) + log y' - log y) * (b (.inl (i, 1)) - y') +
        (η * ℓ (.inl (i, 2)) + log y' - log y) * (b (.inl (i, 2)) - y') +
        (η * ℓ (.inl (i, 3)) + log y' - log y) * (b (.inl (i, 3)) - y') +
        (η * ℓ (.inl (i, 4)) + log z' - log z) * (b (.inl (i, 4)) - z') =
      (b (.inr 0) - z') * (η * ℓ (.inl (i, 4)) + log z' - log z - gX) := by
    intro i
    obtain ⟨hX, hY1, hY2, hY3⟩ := hℓ.1 i
    obtain ⟨h2, h3, h4, h5⟩ := hb.2.1 i
    rw [hX, hY1, hY2, hY3, hA, hB]
    linear_combination gX * h5 + gX * h2 + gX * h3 +
      (η * ℓ (.inl (i, 4)) + log z' - log z - gX) * h4 - gX * hyy
  rw [sum_coord]
  simp only [curve_X, curve_Y1, curve_Y2, curve_Y3, curve_Z, curve_P, curve_Q]
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    nsmul_eq_mul, nsmul_eq_mul, hℓ.2]
  have hPQ := hb.2.2
  unfold level lossZP
  rw [hA, hB]
  linear_combination (η * ∑ i, ℓ (.inl (i, 4)) + m * (log z' - log z) - m * gX + η * ℓ (.inr 0) +
    log z' - log z) * hPQ

/-- **Steps along the curve** [SSKM26, Lemma 48], corrected. For a loss `ℓ` of the construction,
`E > 0` and `q, q' ∈ (0, 2 / d)`, the point `W(e^η E, q')` is a `q' h(r)`-approximate mirror
descent step on the polytope from `W(E, q)`, with the negative entropy, learning rate `η` and loss
`ℓ`, where `r = f(e^η E, q') - f(E, q) - η S(ℓ)` and `h(r) = e^{-r} - 1 + r`. With
`f(e^η E, q') = f(E, q) + η S(ℓ)` it is the exact step; with `q' = q` it is the frozen step. -/
lemma isApproxMirrorDescentStep_curve {η E E' q q' : ℝ} {ℓ : Fin m × Fin 5 ⊕ Fin 2 → ℝ}
    (hE : 0 < E) (hE' : E' = exp η * E) (hq : q ∈ Ioo 0 (2 / (5 * m + 2) : ℝ))
    (hq' : q' ∈ Ioo 0 (2 / (5 * m + 2) : ℝ)) (hℓ : IsShapedLoss ℓ) :
    IsApproxMirrorDescentStep (polytope m) negEntropy η
      (∑ j, ℓ j • ContinuousLinearMap.proj j) (curve m E q)
      (∑ j, log (curve m E q j) • ContinuousLinearMap.proj j)
      (q' * expRem (level m E' q' - level m E q - η * lossZP ℓ)) (curve m E' q') := by
  have hE'pos : 0 < E' := hE' ▸ mul_pos (exp_pos η) hE
  refine ⟨curve_mem_polytope hE'pos hq', fun b hb ↦ ?_⟩
  have hgap := objective_sub_objective η ℓ (curve m E q) (curve m E' q') b
  rw [sum_mul_sub_curve hE hE' hq hq' hℓ hb] at hgap
  set r := level m E' q' - level m E q - η * lossZP ℓ
  have hδ : b (.inr 1) * log (b (.inr 1)) - b (.inr 1) * log q' - b (.inr 1) + q' ≤
      ∑ j, (b j * log (b j) - b j * log (curve m E' q' j) - b j + curve m E' q' j) :=
    Finset.single_le_sum (f := fun j ↦ b j * log (b j) - b j * log (curve m E' q' j) - b j +
      curve m E' q' j) (fun j _ ↦ entropyGap_nonneg (hb.1 j) (curve_pos hE'pos hq' j))
      (Finset.mem_univ (Sum.inr 1 : Fin m × Fin 5 ⊕ Fin 2))
  have hconj := neg_mul_expRem_le r (hb.1 (.inr 1)) hq'.1
  linarith

/-! ### The trajectory -/

/-- The coordinate `q_n` of the trajectory of Theorem 8 of [SSKM26], for the losses `ℓ`:
`q_0 = 1 / d`; from round `τ` on, the step keeps `q` (frozen step) if `q h(r) ≤ ε`; otherwise it
is the exact step, `q_{n+1} = f_{n+1}⁻¹ (f_n(q_n) + η S(ℓ n))`, with `f_n = f(e^{η n}, ·)`. -/
noncomputable def trajQ (m : ℕ) (η ε : ℝ) (τ : ℕ) : ℕ → (ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ) → ℝ
  | 0, _ => (5 * m + 2 : ℝ)⁻¹
  | n + 1, ℓ =>
    if τ ≤ n ∧ trajQ m η ε τ n ℓ * expRem (level m (exp (η * ↑(n + 1))) (trajQ m η ε τ n ℓ) -
        level m (exp (η * n)) (trajQ m η ε τ n ℓ) - η * lossZP (ℓ n)) ≤ ε then
      trajQ m η ε τ n ℓ
    else levelInv m (exp (η * ↑(n + 1)))
      (level m (exp (η * n)) (trajQ m η ε τ n ℓ) + η * lossZP (ℓ n))

/-- The play of round `n` of the trajectory of Theorem 8 of [SSKM26], for the losses `ℓ`: the
point `W(e^{η n}, q_n)` of the curve. -/
noncomputable def traj (m : ℕ) (η ε : ℝ) (τ : ℕ) (n : ℕ) (ℓ : ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ) :
    Fin m × Fin 5 ⊕ Fin 2 → ℝ :=
  curve m (exp (η * n)) (trajQ m η ε τ n ℓ)

variable {η ε : ℝ} {τ : ℕ}

lemma trajQ_zero (ℓ : ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ) : trajQ m η ε τ 0 ℓ = (5 * m + 2 : ℝ)⁻¹ := rfl

lemma trajQ_succ (n : ℕ) (ℓ : ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ) :
    trajQ m η ε τ (n + 1) ℓ =
      if τ ≤ n ∧ trajQ m η ε τ n ℓ * expRem (level m (exp (η * ↑(n + 1))) (trajQ m η ε τ n ℓ) -
          level m (exp (η * n)) (trajQ m η ε τ n ℓ) - η * lossZP (ℓ n)) ≤ ε then
        trajQ m η ε τ n ℓ
      else levelInv m (exp (η * ↑(n + 1)))
        (level m (exp (η * n)) (trajQ m η ε τ n ℓ) + η * lossZP (ℓ n)) := rfl

lemma exp_mul_succ (η : ℝ) (n : ℕ) : exp (η * ↑(n + 1)) = exp η * exp (η * n) := by
  rw [← exp_add]
  push_cast
  ring_nf

/-- The coordinate `q_n` stays in `(0, 2 / d)`. -/
lemma trajQ_mem (n : ℕ) (ℓ : ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ) :
    trajQ m η ε τ n ℓ ∈ Ioo 0 (2 / (5 * m + 2) : ℝ) := by
  induction n with
  | zero =>
    have hd : (0 : ℝ) < 5 * m + 2 := by positivity
    refine ⟨inv_pos.mpr hd, ?_⟩
    rw [trajQ_zero, div_eq_mul_inv]
    linarith [inv_pos.mpr hd]
  | succ n ih =>
    rw [trajQ_succ]
    split_ifs
    exacts [ih, levelInv_mem (exp_pos _) _]

/-- The trajectory starts at the uniform point. -/
lemma traj_zero (ℓ : ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ) :
    traj m η ε τ 0 ℓ = fun _ ↦ (5 * m + 2 : ℝ)⁻¹ := by
  simp [traj, trajQ_zero, curve_one_inv]

/-- The plays of the trajectory have positive coordinates. -/
lemma traj_pos (n : ℕ) (ℓ : ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ) (j : Fin m × Fin 5 ⊕ Fin 2) :
    0 < traj m η ε τ n ℓ j :=
  curve_pos (exp_pos _) (trajQ_mem n ℓ) j

/-- **The trajectory of Theorem 8 is `ε`-approximate** [SSKM26, Lemma 48], corrected: for every
loss sequence of the construction, each play is an `ε`-approximate mirror descent step on the
polytope from the previous one. -/
lemma isApproxMirrorDescentStep_traj (hε : 0 ≤ ε) {ℓ : ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ}
    (hℓ : ∀ t, IsShapedLoss (ℓ t)) (n : ℕ) :
    IsApproxMirrorDescentStep (polytope m) negEntropy η
      (∑ j, ℓ n j • ContinuousLinearMap.proj j) (traj m η ε τ n ℓ)
      (∑ j, log (traj m η ε τ n ℓ j) • ContinuousLinearMap.proj j) ε
      (traj m η ε τ (n + 1) ℓ) := by
  have hstep := fun q' (hq' : q' ∈ Ioo 0 (2 / (5 * m + 2) : ℝ)) ↦
    isApproxMirrorDescentStep_curve (exp_pos _) (exp_mul_succ η n)
      (trajQ_mem (η := η) (ε := ε) (τ := τ) n ℓ) hq' (hℓ n)
  unfold traj
  rw [trajQ_succ]
  split_ifs with h
  · exact (hstep _ (trajQ_mem n ℓ)).mono h.2
  · refine (hstep _ (levelInv_mem (exp_pos _) _)).mono ?_
    rw [level_levelInv (exp_pos _)]
    simpa using hε

/-- Each coordinate `q_n` is a measurable function of the losses. -/
@[fun_prop]
lemma measurable_trajQ (n : ℕ) : Measurable (trajQ m η ε τ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hS : Measurable fun ℓ : ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ ↦ lossZP (ℓ n) :=
      measurable_lossZP.comp (measurable_pi_apply n)
    have hlev : ∀ E, Measurable fun ℓ ↦ level m E (trajQ m η ε τ n ℓ) :=
      fun E ↦ (measurable_level m E).comp ih
    have hset : MeasurableSet {ℓ | τ ≤ n ∧ trajQ m η ε τ n ℓ *
        expRem (level m (exp (η * ↑(n + 1))) (trajQ m η ε τ n ℓ) -
          level m (exp (η * n)) (trajQ m η ε τ n ℓ) - η * lossZP (ℓ n)) ≤ ε} := by
      rw [Set.ofPred_and]
      refine (MeasurableSet.const _).inter (measurableSet_le ?_ measurable_const)
      exact ih.mul (measurable_expRem.comp (((hlev _).sub (hlev _)).sub (hS.const_mul η)))
    exact Measurable.ite hset ih
      ((measurable_levelInv (exp_pos _)).comp ((hlev _).add (hS.const_mul η)))

/-- Each play is a measurable function of the losses. -/
lemma measurable_traj (n : ℕ) : Measurable (traj m η ε τ n) :=
  (continuous_curve m _).measurable.comp (measurable_trajQ n)

/-- Each coordinate `q_n` depends only on the losses of the rounds before `n`. -/
lemma trajQ_congr (n : ℕ) {ℓ ℓ' : ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ} (h : ∀ s < n, ℓ s = ℓ' s) :
    trajQ m η ε τ n ℓ = trajQ m η ε τ n ℓ' := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [trajQ_succ, trajQ_succ, ih fun s hs ↦ h s (by omega), h n (by omega)]

/-- Each play depends only on the losses of the rounds before it. -/
lemma traj_congr (n : ℕ) {ℓ ℓ' : ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ} (h : ∀ s < n, ℓ s = ℓ' s) :
    traj m η ε τ n ℓ = traj m η ε τ n ℓ' := by
  rw [traj, traj, trajQ_congr n h]

end Schlisselberg2026Hidden.PolytopeLower
