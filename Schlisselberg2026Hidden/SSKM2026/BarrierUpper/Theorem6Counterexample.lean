/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.Analysis.Convex.PowerBarrier
public import LMLExplore.Analysis.Convex.Simplex
public import LMLExplore.OnlineLearning.Regret

/-!
# The statement of Theorem 6 frozen at the end of phase 1 is false

As frozen at the end of phase 1,
`Schlisselberg2026Hidden.approxMirrorDescent_regret_le_of_isPowerBarrier` bounded the regret
against every `u ∈ K` when `r` is right-continuous at `0`. The definition of a power barrier
(`LMLExplore.IsPowerBarrier`) constrains `r` on `(0, 1)` only, and `r 1` enters `D_R(u, w₁)` when
`u` is a vertex of the simplex. Changing a Tsallis entropy at `1` alone keeps a power barrier
that is right-continuous at `0` (`LMLExplore.IsPowerBarrier.congr`), and makes `D_R(u, w₁)`
negative for a vertex `u`. With `T = 0` rounds the regret is `0`, and the bound reads
`0 ≤ D_R(u, w₁) / η`, which fails. The theorem now also asks `r` to be left-continuous at `1`
(`notes/statement-corrections.md`, Theorem 6).

## Main statements

* `Schlisselberg2026Hidden.exists_not_regret_le_of_isPowerBarrier`: the counterexample.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

/-- **A counterexample to the statement of Theorem 6 frozen at the end of phase 1**
(`approxMirrorDescent_regret_le_of_isPowerBarrier`). Take `α = Fin 2`, `A w = w 0 + w 1` and
`b = 1`, so that `K` is the simplex, the Tsallis entropy of index `1 / 2` changed to `-10` at `1`,
the vertex `u = (1, 0)`, `η = 1`, `ε = 0`, `T = 0`, the losses `0` and the constant trajectory at
the uniform point. The function is a power barrier with exponent `3 / 2` and constants `1 / 2`,
right-continuous at `0`; `K` lies in the simplex and contains the uniform point and `u`; the other
hypotheses (`0 < η`, the bound on the losses, the threshold on `ε`, the steps) hold trivially for
`T = 0`. The conclusion fails: the regret is `0` and the bound is
`D_R(u, w₁) / η = -10 - 2 r (1 / 2) ≤ -8`. -/
lemma exists_not_regret_le_of_isPowerBarrier :
    ∃ r : ℝ → ℝ, IsPowerBarrier (2 - 1 / 2) (1 / 2) (1 / 2) r ∧
      ContinuousWithinAt r (Set.Ici 0) 0 ∧
      {w : Fin 2 → ℝ | (∀ i, 0 ≤ w i) ∧
        (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0 +
          LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1) w = 1} ⊆ simplex (Fin 2) ∧
      (fun _ ↦ (Fintype.card (Fin 2) : ℝ)⁻¹) ∈ {w : Fin 2 → ℝ | (∀ i, 0 ≤ w i) ∧
        (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0 +
          LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1) w = 1} ∧
      ![1, 0] ∈ {w : Fin 2 → ℝ | (∀ i, 0 ≤ w i) ∧
        (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0 +
          LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1) w = 1} ∧
      ¬ regret (fun _ w ↦ ∑ i, (0 : ℝ) * w i)
          (fun (_ : ℕ) (_ : Fin 2) ↦ (Fintype.card (Fin 2) : ℝ)⁻¹) ![1, 0] 0 ≤
        bregDiv (fun w ↦ ∑ i, r (w i)) ![1, 0] (fun _ ↦ (Fintype.card (Fin 2) : ℝ)⁻¹)
            (∑ i, deriv r (Fintype.card (Fin 2) : ℝ)⁻¹ • ContinuousLinearMap.proj i :
              (Fin 2 → ℝ) →L[ℝ] ℝ) / 1 +
          (1 + 1 / (1 / 2)) * 1 * ((0 : ℕ) : ℝ) := by
  set ts : ℝ → ℝ := fun x ↦ (x - x ^ (1 / 2 : ℝ)) / (1 - 1 / 2) with hts
  set r : ℝ → ℝ := fun x ↦ if x = 1 then -10 else ts x with hr
  have hrts : ∀ x, x ≠ 1 → r x = ts x := fun x hx ↦ by simp [hr, hx]
  have hbar : IsPowerBarrier (2 - 1 / 2) (1 / 2) (1 / 2) r :=
    (isPowerBarrier_tsallis (by norm_num) (by norm_num)).congr fun x hx ↦ hrts x hx.2.ne
  have hcont : ContinuousWithinAt r (Set.Ici 0) 0 := by
    have h1 : ContinuousAt ts 0 :=
      (continuousAt_id.sub (continuousAt_rpow_const 0 (1 / 2) (Or.inr (by norm_num)))).div_const
        _
    exact (h1.congr ((eventually_ne_nhds (by norm_num : (0 : ℝ) ≠ 1)).mono fun x hx ↦
      (hrts x hx).symm)).continuousWithinAt
  have hcard : (Fintype.card (Fin 2) : ℝ)⁻¹ = 1 / 2 := by simp
  have h1 : r 1 = -10 := by simp [hr]
  have h0 : r 0 = 0 := by
    rw [hrts 0 (by norm_num), hts]
    simp
  have hhalf : -1 ≤ r (1 / 2) := by
    rw [hrts (1 / 2) (by norm_num), hts]
    have : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) ≤ 1 := rpow_le_one (by norm_num) (by norm_num) (by norm_num)
    simp only
    rw [le_div_iff₀ (by norm_num)]
    linarith
  refine ⟨r, hbar, hcont, ?_, ?_, ?_, ?_⟩
  · intro w hw
    refine mem_simplex_iff.mpr ⟨hw.1, ?_⟩
    simpa [Fin.sum_univ_two] using hw.2
  · refine ⟨fun _ ↦ by positivity, ?_⟩
    simp only [LinearMap.add_apply, LinearMap.coe_proj, Function.eval, hcard]
    norm_num
  · refine ⟨fun i ↦ ?_, by simp⟩
    fin_cases i <;> simp
  -- the bound is negative
  rw [regret_def]
  simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, mul_zero, add_zero, div_one,
    not_le, hcard]
  rw [show (∑ i : Fin 2, deriv r (1 / 2) • ContinuousLinearMap.proj i : (Fin 2 → ℝ) →L[ℝ] ℝ) =
    ∑ i : Fin 2, deriv r ((fun _ ↦ (1 / 2 : ℝ)) i) • ContinuousLinearMap.proj i from rfl,
    bregDiv_sum_apply]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [h1, h0]
  linarith

end Schlisselberg2026Hidden
