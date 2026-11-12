/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent
public import LMLExplore.Analysis.Convex.NegEntropy
public import Mathlib.Probability.ProductMeasure
public import Schlisselberg2026Hidden.SSKM2026.Theorem49

/-!
# Theorem 8 of [SSKM26]: on subsets of the simplex, stochastic losses do not help

With the negative entropy and i.i.d. losses, Theorem 7 of [SSKM26] shows that polynomially small
errors suffice on the simplex. This fails on its polyhedral subsets: for every `η` and every
`ε ≤ 1/3` with `100 η log (1/ε) ≤ 1`, there is a polytope `K` in standard form, a subset of the
simplex of dimension at most `100 log (1/ε)` containing the uniform point, a law of losses in
`[-1, 1]^d`, and an `ε`-approximate trajectory of mirror descent on `K` (a measurable function of
the past losses) whose expected regret against a point of `K` is at least
`T √(η / log (1/ε)) / 20`, and at least `D_R(w*, w₁) / (6 η) + T √(η / log (1/ε)) / 20` for
`η T ≥ 1`. Unless `ε` is exponentially small in `1/η`, this is far above the `O(√T)` of the
simplex.

The polytope is the paper's, in dimension `5 m + 2` with `m = ⌈16 log (1/ε)⌉`. The losses are
those of the paper with its Gaussian coordinates replaced by independent Rademacher signs and its
coordinate of mean `√(η d)` made constant. The trajectory follows exact steps for `⌈3/η⌉` rounds,
then freezes one coordinate as long as the frozen step is `ε`-approximate.

The paper states the theorem with the polytope and the law chosen before `ε`, for every `ε > 0`,
with Gaussian (unbounded) losses and `Ω(D_R(w, w₁) / η + T √(η / log (1/ε)))`; the dimension of
the polytope is part of the claim, which is otherwise implied by Theorem 35 of [SSKM26] in high
dimension (`notes/paper-errata.md`).

The construction is carried out on the index type `Fin m × Fin 5 ⊕ Fin 2`
(`Schlisselberg2026Hidden.SSKM2026.Lemma44`, `Lemma48`, `Lemma47`, `Theorem49`); this file chooses
the parameters `m = ⌈16 log (1/ε)⌉`, `τ = ⌈3/η⌉`, `μ = √(η d)`, and transports the construction to
`Fin d` along an enumeration of the coordinates.

## Main statements

* `Schlisselberg2026Hidden.exists_approxMirrorDescent_le_integral_regret_polytope`:
  [SSKM26, Theorem 8], corrected.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real MeasureTheory Matrix

namespace Schlisselberg2026Hidden

namespace PolytopeLower

/-! ### Transport along an enumeration of the coordinates -/

section Transport

variable {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)

/-- The objective of a step, transported along `e`. -/
lemma objective_comp_symm (η : ℝ) (ℓ a : α → ℝ) (v : β → ℝ) :
    η * (∑ j, ℓ (e.symm j) • ContinuousLinearMap.proj j : (β → ℝ) →L[ℝ] ℝ) v +
        bregDiv negEntropy v (fun j ↦ a (e.symm j))
          (∑ j, log (a (e.symm j)) • ContinuousLinearMap.proj j : (β → ℝ) →L[ℝ] ℝ) =
      η * (∑ i, ℓ i • ContinuousLinearMap.proj i : (α → ℝ) →L[ℝ] ℝ) (fun i ↦ v (e i)) +
        bregDiv negEntropy (fun i ↦ v (e i)) a
          (∑ i, log (a i) • ContinuousLinearMap.proj i : (α → ℝ) →L[ℝ] ℝ) := by
  simp only [bregDiv, negEntropy_def, sum_smul_proj_apply, Pi.sub_apply]
  have h1 : ∑ j, ℓ (e.symm j) * v j = ∑ i, ℓ i * v (e i) :=
    (Fintype.sum_equiv e _ _ fun i ↦ by simp).symm
  have h2 : ∑ j, (v j * log (v j) - v j) = ∑ i, (v (e i) * log (v (e i)) - v (e i)) :=
    (Fintype.sum_equiv e _ _ fun i ↦ rfl).symm
  have h3 : ∑ j, (a (e.symm j) * log (a (e.symm j)) - a (e.symm j)) =
      ∑ i, (a i * log (a i) - a i) := Fintype.sum_equiv e.symm _ _ fun j ↦ rfl
  have h4 : ∑ j, log (a (e.symm j)) * (v j - a (e.symm j)) =
      ∑ i, log (a i) * (v (e i) - a i) := (Fintype.sum_equiv e _ _ fun i ↦ by simp).symm
  rw [h1, h2, h3, h4]

/-- Approximate mirror descent steps with the negative entropy, transported along `e`. -/
lemma isApproxMirrorDescentStep_comp_symm {K : Set (α → ℝ)} {η ε : ℝ} {ℓ a x : α → ℝ}
    (h : IsApproxMirrorDescentStep K negEntropy η (∑ i, ℓ i • ContinuousLinearMap.proj i) a
      (∑ i, log (a i) • ContinuousLinearMap.proj i) ε x) :
    IsApproxMirrorDescentStep {w | (fun i ↦ w (e i)) ∈ K} negEntropy η
      (∑ j, ℓ (e.symm j) • ContinuousLinearMap.proj j) (fun j ↦ a (e.symm j))
      (∑ j, log (a (e.symm j)) • ContinuousLinearMap.proj j) ε (fun j ↦ x (e.symm j)) := by
  refine ⟨by simpa using h.mem, fun b hb ↦ ?_⟩
  rw [objective_comp_symm, objective_comp_symm]
  simpa using h.le_add _ hb

/-- The Bregman divergence of the negative entropy from a constant point, transported along `e`. -/
lemma bregDiv_negEntropy_comp_symm (x : α → ℝ) (c : ℝ) :
    bregDiv negEntropy (fun j ↦ x (e.symm j)) (fun _ ↦ c)
        (∑ j, log c • ContinuousLinearMap.proj j : (β → ℝ) →L[ℝ] ℝ) =
      bregDiv negEntropy x (fun _ ↦ c)
        (∑ i, log c • ContinuousLinearMap.proj i : (α → ℝ) →L[ℝ] ℝ) := by
  simp only [bregDiv, negEntropy_def, sum_smul_proj_apply, Pi.sub_apply]
  have h1 : ∑ j, (x (e.symm j) * log (x (e.symm j)) - x (e.symm j)) =
      ∑ i, (x i * log (x i) - x i) := Fintype.sum_equiv e.symm _ _ fun j ↦ rfl
  have h2 : ∑ _j : β, (c * log c - c) = ∑ _i : α, (c * log c - c) :=
    Fintype.sum_equiv e.symm _ _ fun j ↦ rfl
  have h3 : ∑ j, log c * (x (e.symm j) - c) = ∑ i, log c * (x i - c) :=
    Fintype.sum_equiv e.symm _ _ fun j ↦ rfl
  rw [h1, h2, h3]

/-- The regret for linear losses, transported along `e`. -/
lemma regret_comp_symm (ℓ x : ℕ → α → ℝ) (u : α → ℝ) (T : ℕ) :
    regret (fun t w ↦ ∑ j, ℓ t (e.symm j) * w j) (fun t j ↦ x t (e.symm j)) (fun j ↦ u (e.symm j))
        T = regret (fun t w ↦ ∑ i, ℓ t i * w i) x u T := by
  simp only [regret_def]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [Fintype.sum_equiv e.symm _ (fun i ↦ ℓ t i * x t i) fun j ↦ rfl,
    Fintype.sum_equiv e.symm _ (fun i ↦ ℓ t i * u i) fun j ↦ rfl]

lemma mem_simplex_of_comp {w : β → ℝ} (h : (fun i ↦ w (e i)) ∈ simplex α) : w ∈ simplex β := by
  rw [mem_simplex_iff] at h ⊢
  refine ⟨fun j ↦ by simpa using h.1 (e.symm j), ?_⟩
  rw [← h.2]
  exact (Equiv.sum_comp e w).symm

end Transport

/-- A finite family of linear equations on `n → ℝ` is a matrix equation. -/
lemma exists_matrix_mulVec_eq_iff {n R : Type*} [Fintype n] [Finite R]
    (ψ : R → (n → ℝ) →ₗ[ℝ] ℝ) (c : R → ℝ) :
    ∃ (k : ℕ) (A : Matrix (Fin k) n ℝ) (b : Fin k → ℝ), ∀ w, A *ᵥ w = b ↔ ∀ ρ, ψ ρ w = c ρ := by
  classical
  have := Fintype.ofFinite R
  let eR := Fintype.equivFin R
  set A : Matrix (Fin (Fintype.card R)) n ℝ :=
    Matrix.of fun r i ↦ ψ (eR.symm r) (fun j ↦ if i = j then 1 else 0)
  refine ⟨Fintype.card R, A, fun r ↦ c (eR.symm r), fun w ↦ ?_⟩
  have hA : ∀ r, (A *ᵥ w) r = ψ (eR.symm r) w := by
    intro r
    rw [LinearMap.pi_apply_eq_sum_univ (ψ (eR.symm r)) w]
    simp [A, Matrix.mulVec, dotProduct, mul_comm]
  rw [funext_iff]
  simp only [hA]
  exact ⟨fun h ρ ↦ by simpa using h (eR ρ), fun h r ↦ h _⟩

/-! ### The parameters -/

/-- The parameters of the construction, for `0 < ε ≤ 1 / 3` and `100 η log (1 / ε) ≤ 1`:
`m = ⌈16 log (1 / ε)⌉ ≥ 17`, `d = 5 m + 2 ≤ 100 log (1 / ε)`, `η d ≤ 1`, and `τ = ⌈3 / η⌉` has
`3 ≤ η τ ≤ 7 / 2` [SSKM26, Appendix G], corrected (erratum E28). -/
lemma params {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (hε' : ε ≤ 1 / 3)
    (hηε : 100 * η * log (1 / ε) ≤ 1) :
    1 < log (1 / ε) ∧ 17 ≤ ⌈16 * log (1 / ε)⌉₊ ∧ 16 * log (1 / ε) ≤ ⌈16 * log (1 / ε)⌉₊ ∧
      (5 * ⌈16 * log (1 / ε)⌉₊ + 2 : ℝ) ≤ 100 * log (1 / ε) ∧
      η * (5 * ⌈16 * log (1 / ε)⌉₊ + 2) ≤ 1 ∧ 3 ≤ η * ⌈3 / η⌉₊ ∧ η * ⌈3 / η⌉₊ ≤ 7 / 2 := by
  have hL : 1 < log (1 / ε) := by
    rw [lt_log_iff_exp_lt (by positivity)]
    have h3 : 3 ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
    linarith [exp_one_lt_d9]
  set L := log (1 / ε)
  set m := ⌈16 * L⌉₊
  have hm1 : 16 * L ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) < 16 * L + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm17 : 17 ≤ m := by
    have : (16 : ℝ) < m := by linarith
    exact_mod_cast this
  have hdL : (5 * m + 2 : ℝ) ≤ 100 * L := by linarith
  have hηd : η * (5 * m + 2) ≤ 1 := by nlinarith
  have hτ1 : 3 / η ≤ ⌈3 / η⌉₊ := Nat.le_ceil _
  have hτ2 : (⌈3 / η⌉₊ : ℝ) < 3 / η + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm17' : (17 : ℝ) ≤ m := by exact_mod_cast hm17
  refine ⟨hL, hm17, hm1, hdL, hηd, ?_, ?_⟩
  · calc (3 : ℝ) = η * (3 / η) := by field_simp
      _ ≤ η * ⌈3 / η⌉₊ := by gcongr
  · have : η * ⌈3 / η⌉₊ < 3 + η := by
      calc η * ⌈3 / η⌉₊ < η * (3 / η + 1) := by gcongr
        _ = 3 + η := by field_simp
    nlinarith

/-- The constant of the main term: `√(η / L) / 20 ≤ √(η d) / (2 d)` when `d ≤ 100 L`. -/
lemma sqrt_div_le {η L d : ℝ} (hη : 0 < η) (hL : 0 < L) (hd : 0 < d) (hdL : d ≤ 100 * L) :
    √(η / L) / 20 ≤ √(η * d) / (2 * d) := by
  have h1 : √(η * d) / (2 * d) = √(η / d) / 2 := by
    rw [show η / d = η * d / d ^ 2 by field_simp, Real.sqrt_div' _ (sq_nonneg d),
      Real.sqrt_sq hd.le]
    field_simp
  have h2 : √(η / L) ≤ 10 * √(η / d) := by
    have h10 : (10 : ℝ) = √100 := by
      rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h10, ← Real.sqrt_mul (by norm_num)]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ hL, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hd]
    nlinarith
  rw [h1]
  linarith

end PolytopeLower

/-- **On subsets of the simplex, stochastic losses do not help** [SSKM26, Theorem 8], corrected.
Let `η > 0` and `0 < ε ≤ 1/3` with `100 η log (1/ε) ≤ 1`. There are a dimension
`d ≤ 100 log (1/ε)`, a polytope `K = {w ≥ 0, A w = b}` contained in the simplex and containing the
uniform point, a probability law `ν` of losses in `[-1, 1]^d`, plays `play t ℓ` that depend
measurably on the losses `ℓ s` of the rounds `s < t` only, and a comparator `w* ∈ K`, such that
for i.i.d. losses of law `ν`, almost surely the plays are an `ε`-approximate trajectory of mirror
descent on `K` with the negative entropy and learning rate `η`, started at the uniform point and
with positive coordinates, and for every horizon `T` the expected regret against `w*` is at least
`T √(η / log (1/ε)) / 20`, and at least `D_R(w*, w₁) / (6 η) + T √(η / log (1/ε)) / 20` if
`η T ≥ 1`. -/
theorem exists_approxMirrorDescent_le_integral_regret_polytope {η ε : ℝ} (hη : 0 < η)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 3) (hηε : 100 * η * log (1 / ε) ≤ 1) :
    ∃ d : ℕ, (d : ℝ) ≤ 100 * log (1 / ε) ∧
    ∃ (k : ℕ) (A : Matrix (Fin k) (Fin d) ℝ) (b : Fin k → ℝ) (K : Set (Fin d → ℝ)),
      K = {w | (∀ i, 0 ≤ w i) ∧ A *ᵥ w = b} ∧ K ⊆ simplex (Fin d) ∧
      (fun _ ↦ (d : ℝ)⁻¹) ∈ K ∧
    ∃ ν : Measure (Fin d → ℝ), IsProbabilityMeasure ν ∧ (∀ᵐ x ∂ν, ∀ i, x i ∈ Set.Icc (-1) 1) ∧
    ∃ play : ℕ → (ℕ → Fin d → ℝ) → Fin d → ℝ, (∀ t, Measurable (play t)) ∧
      (∀ t ℓ ℓ', (∀ s < t, ℓ s = ℓ' s) → play t ℓ = play t ℓ') ∧
      (∀ᵐ ℓ ∂(Measure.infinitePi fun _ : ℕ ↦ ν), play 0 ℓ = (fun _ ↦ (d : ℝ)⁻¹) ∧
        (∀ t i, 0 < play t ℓ i) ∧
        ∀ t, IsApproxMirrorDescentStep K negEntropy η (∑ i, ℓ t i • ContinuousLinearMap.proj i)
          (play t ℓ) (∑ i, log (play t ℓ i) • ContinuousLinearMap.proj i) ε (play (t + 1) ℓ)) ∧
    ∃ wStar ∈ K, ∀ T : ℕ,
      T * √(η / log (1 / ε)) / 20 ≤
        ∫ ℓ, regret (fun t w ↦ ∑ i, ℓ t i * w i) (fun t ↦ play t ℓ) wStar T
          ∂(Measure.infinitePi fun _ : ℕ ↦ ν) ∧
      (1 ≤ η * T → bregDiv negEntropy wStar (fun _ ↦ (d : ℝ)⁻¹)
          (∑ i, log (d : ℝ)⁻¹ • ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ) / (6 * η) +
          T * √(η / log (1 / ε)) / 20 ≤
        ∫ ℓ, regret (fun t w ↦ ∑ i, ℓ t i * w i) (fun t ↦ play t ℓ) wStar T
          ∂(Measure.infinitePi fun _ : ℕ ↦ ν)) := by
  classical
  obtain ⟨hL, hm17, hmL, hdL, hηd, hτ3, hτ'⟩ := PolytopeLower.params hη hε hε' hηε
  set m := ⌈16 * log (1 / ε)⌉₊ with hm_def
  set τ := ⌈3 / η⌉₊ with hτ_def
  set μ := √(η * (5 * m + 2)) with hμ_def
  have hμ0 : 0 ≤ μ := Real.sqrt_nonneg _
  have hμ1 : μ ≤ 1 := Real.sqrt_le_one.mpr hηd
  have hm7 : 7 ≤ m := by omega
  -- the enumeration of the coordinates
  set d := Fintype.card (Fin m × Fin 5 ⊕ Fin 2) with hd_def
  have hdm : (d : ℝ) = 5 * m + 2 := by
    rw [hd_def, PolytopeLower.card_coord]
    push_cast
    ring
  let e : (Fin m × Fin 5 ⊕ Fin 2) ≃ Fin d := Fintype.equivFin _
  have hψ : MeasurableEmbedding fun (x : Fin m × Fin 5 ⊕ Fin 2 → ℝ) (j : Fin d) ↦ x (e.symm j) :=
    (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl ℝ)).measurableEmbedding
  have hφ : MeasurableEmbedding
      fun (ℓ : ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ) (t : ℕ) (j : Fin d) ↦ ℓ t (e.symm j) :=
    (MeasurableEquiv.piCongrRight fun _ : ℕ ↦
      MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl ℝ)).measurableEmbedding
  have hmap : (Measure.infinitePi fun _ : ℕ ↦
        (PolytopeLower.lossLaw m μ).map fun (x : Fin m × Fin 5 ⊕ Fin 2 → ℝ) (j : Fin d) ↦
          x (e.symm j)) =
      (Measure.infinitePi fun _ : ℕ ↦ PolytopeLower.lossLaw m μ).map
        fun (ℓ : ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ) (t : ℕ) (j : Fin d) ↦ ℓ t (e.symm j) :=
    (Measure.infinitePi_map_pi _ fun _ ↦ hψ.measurable).symm
  -- the polytope as a matrix equation
  obtain ⟨k, A, b, hAb⟩ := PolytopeLower.exists_matrix_mulVec_eq_iff
    (fun ρ ↦ (PolytopeLower.constraint m ρ).comp (LinearMap.funLeft ℝ ℝ e))
    (PolytopeLower.constraintValue m)
  have hK : {w : Fin d → ℝ | (∀ i, 0 ≤ w i) ∧ A *ᵥ w = b} =
      {w | (fun i ↦ w (e i)) ∈ PolytopeLower.polytope m} := by
    ext w
    rw [PolytopeLower.polytope_eq_setOf_constraint]
    simp only [Set.mem_ofPred_eq, hAb, LinearMap.coe_comp, Function.comp_apply]
    exact and_congr ⟨fun h i ↦ h _, fun h j ↦ by simpa using h (e.symm j)⟩ Iff.rfl
  refine ⟨d, by rw [hdm]; exact hdL, k, A, b, _, rfl, ?_, ?_,
    (PolytopeLower.lossLaw m μ).map fun (x : Fin m × Fin 5 ⊕ Fin 2 → ℝ) (j : Fin d) ↦ x (e.symm j),
    ?_, ?_, fun t ℓ' j ↦ PolytopeLower.traj m η ε τ t (fun s i ↦ ℓ' s (e i)) (e.symm j),
    ?_, ?_, ?_, fun j ↦ PolytopeLower.comparator m (e.symm j), ?_, fun T ↦ ?_⟩
  · -- the polytope lies in the simplex
    rw [hK]
    exact fun w hw ↦
      PolytopeLower.mem_simplex_of_comp e (PolytopeLower.polytope_subset_simplex m hw)
  · -- it contains the uniform point
    rw [hK]
    change (fun _ ↦ (d : ℝ)⁻¹) ∈ PolytopeLower.polytope m
    rw [hdm]
    exact PolytopeLower.uniform_mem_polytope m
  · -- the law is a probability measure
    exact ⟨by rw [Measure.map_apply hψ.measurable MeasurableSet.univ, Set.preimage_univ,
      measure_univ]⟩
  · -- the losses are in `[-1, 1]^d`
    rw [hψ.ae_map_iff]
    filter_upwards [PolytopeLower.ae_mem_Icc (m := m) (abs_le.mpr ⟨by linarith, hμ1⟩)] with x hx i
      using hx (e.symm i)
  · -- the plays are measurable
    intro t
    refine measurable_pi_iff.mpr fun j ↦ (measurable_pi_apply (e.symm j)).comp
      ((PolytopeLower.measurable_traj t).comp (measurable_pi_iff.mpr fun s ↦
        measurable_pi_iff.mpr fun i ↦ (measurable_pi_apply (e i)).comp (measurable_pi_apply s)))
  · -- each play depends on the past losses only
    intro t ℓ ℓ' h
    have : PolytopeLower.traj m η ε τ t (fun s i ↦ ℓ s (e i)) =
        PolytopeLower.traj m η ε τ t (fun s i ↦ ℓ' s (e i)) :=
      PolytopeLower.traj_congr t fun s hs ↦ by simp only [h s hs]
    simp only [this]
  · -- almost surely, the plays are an `ε`-approximate trajectory
    rw [hmap, hφ.ae_map_iff]
    filter_upwards [PolytopeLower.ae_forall_isLawLoss (m := m) (μ := μ)] with ℓ hℓ
    simp only [Equiv.symm_apply_apply]
    refine ⟨?_, fun t i ↦ PolytopeLower.traj_pos t ℓ _, fun t ↦ ?_⟩
    · ext j
      rw [PolytopeLower.traj_zero, hdm]
    · rw [hK]
      exact PolytopeLower.isApproxMirrorDescentStep_comp_symm e
        (PolytopeLower.isApproxMirrorDescentStep_traj (τ := τ) hε.le (fun t ↦ (hℓ t).1) t)
  · -- the comparator lies in the polytope
    rw [hK]
    simpa using PolytopeLower.comparator_mem_polytope m
  · -- the expected regret
    rw [hmap, hφ.integral_map]
    simp only [Equiv.symm_apply_apply, PolytopeLower.regret_comp_symm]
    obtain ⟨h1, h2⟩ := PolytopeLower.le_integral_regret hη hηd hm7 hε hε' hmL hτ3 hτ' hμ0 hμ1 T
    have hd : (0 : ℝ) < 5 * m + 2 := by positivity
    have hmain : T * √(η / log (1 / ε)) / 20 ≤ T * μ / (2 * (5 * m + 2)) := by
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (PolytopeLower.sqrt_div_le hη (by linarith) hd hdL)
        (Nat.cast_nonneg T)
    refine ⟨hmain.trans h1, fun hT ↦ ?_⟩
    rw [hdm, PolytopeLower.bregDiv_negEntropy_comp_symm]
    have hD := PolytopeLower.bregDiv_comparator_uniform_le (m := m) (by omega)
    have hD' : bregDiv negEntropy (PolytopeLower.comparator m) (fun _ ↦ (5 * m + 2 : ℝ)⁻¹)
          (∑ i, log (5 * m + 2 : ℝ)⁻¹ • ContinuousLinearMap.proj i :
            (Fin m × Fin 5 ⊕ Fin 2 → ℝ) →L[ℝ] ℝ) / (6 * η) ≤
        3 * m / (2 * (5 * m + 2) * η) := by
      calc _ ≤ 9 * m / (5 * m + 2) / (6 * η) := by gcongr
        _ = 3 * m / (2 * (5 * m + 2) * η) := by field_simp; ring
    calc _ ≤ 3 * m / (2 * (5 * m + 2) * η) + T * μ / (2 * (5 * m + 2)) := by linarith
      _ ≤ _ := h2 hT

end Schlisselberg2026Hidden
