/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.SSKM2026.Lemma47
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Theorem 49 of [SSKM26]: the expected regret of the trajectory of Theorem 8

The losses of Theorem 8 of [SSKM26] are i.i.d. over the rounds, with independent coordinates:
`0` on the `X`- and `Q`-coordinates, `1` on the `Y`-coordinates, `μ` on `P`, and centred noise on
the `Z`-coordinates. The paper takes Gaussian noise and a Gaussian `P`-coordinate; we take
independent Rademacher signs and the constant `μ`, so that the losses lie in `[-1, 1]^d`
(variant 8-B of `notes/constants-polytope-lower.md`, decided with the user).

The paper's hardness event (Lemma 45 of [SSKM26]) does not have probability `Ω(1)` (erratum E30),
and its Theorem 49 computes the expected regret on that event although the event depends on the
losses of the same rounds (erratum E34). The corrected argument rests on one symmetry: flipping the
signs of the `Z`-coordinates of a set of rounds preserves the law of the losses
(`PolytopeLower.measurePreserving_flipZ`). Hence
* the median event `{G_n ≤ n μ}`, `G_n = ∑_{s<n} S(ℓ s)`, has probability at least `1 / 2`;
* the loss of a `Z`-coordinate of round `t` is uncorrelated with every function of the losses of
  the other rounds, in particular with the play of round `t`, so the expected regret is
  `∑_{t<T} (3 m E[y_t] + μ E[2 / d - q_t])` exactly.

On the median event of `min(t, τ)` rounds the play of round `t` has `q_t ≤ 1 / d`
(`PolytopeLower.trajQ_le_inv`), so `E[2 / d - q_t] ≥ 1 / (2 d)`; and the `Y`-coordinates give at
least `3 m / (2 d η)` when `η T ≥ 1`.

## Main definitions

* `PolytopeLower.rademacher`: the uniform law on `{-1, 1}`.
* `PolytopeLower.lossLaw m μ`: the law of the losses.

## Main statements

* `PolytopeLower.half_le_measureReal_sum_le_zero`: [SSKM26, Lemma 45], corrected: the median
  event has probability at least `1 / 2`.
* `PolytopeLower.integral_regret_eq`: the expected regret, computed exactly.
* `PolytopeLower.le_integral_regret`: [SSKM26, Theorem 49], corrected.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Real Set MeasureTheory
open scoped ENNReal

namespace Schlisselberg2026Hidden.PolytopeLower

variable {m : ℕ} {μ : ℝ}

/-! ### The law of the losses -/

/-- The Rademacher law, uniform on `{-1, 1}`. -/
noncomputable def rademacher : Measure ℝ := (2⁻¹ : ℝ≥0∞) • (Measure.dirac (-1) + Measure.dirac 1)

instance : IsProbabilityMeasure rademacher := ⟨by
  simp [rademacher, ENNReal.inv_two_add_inv_two]⟩

lemma map_neg_one_mul_rademacher : rademacher.map (fun x ↦ -1 * x) = rademacher := by
  have hf : Measurable fun x : ℝ ↦ -1 * x := measurable_const_mul _
  rw [rademacher, Measure.map_smul _ hf.aemeasurable, Measure.map_add _ _ hf,
    Measure.map_dirac, Measure.map_dirac, add_comm]
  norm_num

lemma ae_dirac_eq_self (c : ℝ) : ∀ᵐ y ∂(Measure.dirac c), y = c := by
  rw [Filter.Eventually, ae_dirac_eq]
  exact Filter.eventually_pure.mpr rfl

lemma ae_abs_le_one_rademacher : ∀ᵐ y ∂rademacher, |y| ≤ 1 := by
  refine Measure.ae_smul_measure (ae_add_measure_iff.mpr ⟨?_, ?_⟩) _
  · filter_upwards [ae_dirac_eq_self (-1)] with y hy
    simp [hy]
  · filter_upwards [ae_dirac_eq_self 1] with y hy
    simp [hy]

/-- The law of each coordinate of the losses: `δ₀` on `X` and `Q`, `δ₁` on `Y`, the Rademacher law
on `Z` and `δ_μ` on `P`. -/
noncomputable def coordLaw (m : ℕ) (μ : ℝ) : Fin m × Fin 5 ⊕ Fin 2 → Measure ℝ :=
  Sum.elim (fun p ↦ ![Measure.dirac 0, Measure.dirac 1, Measure.dirac 1, Measure.dirac 1,
    rademacher] p.2) ![Measure.dirac μ, Measure.dirac 0]

instance (j : Fin m × Fin 5 ⊕ Fin 2) : IsProbabilityMeasure (coordLaw m μ j) := by
  match j with
  | .inl (_, 0) => exact (inferInstance : IsProbabilityMeasure (Measure.dirac (0 : ℝ)))
  | .inl (_, 1) => exact (inferInstance : IsProbabilityMeasure (Measure.dirac (1 : ℝ)))
  | .inl (_, 2) => exact (inferInstance : IsProbabilityMeasure (Measure.dirac (1 : ℝ)))
  | .inl (_, 3) => exact (inferInstance : IsProbabilityMeasure (Measure.dirac (1 : ℝ)))
  | .inl (_, 4) => exact (inferInstance : IsProbabilityMeasure rademacher)
  | .inr 0 => exact (inferInstance : IsProbabilityMeasure (Measure.dirac μ))
  | .inr 1 => exact (inferInstance : IsProbabilityMeasure (Measure.dirac (0 : ℝ)))

/-- The law of the losses of Theorem 8 of [SSKM26], with independent coordinates
(`PolytopeLower.coordLaw`). -/
noncomputable def lossLaw (m : ℕ) (μ : ℝ) : Measure (Fin m × Fin 5 ⊕ Fin 2 → ℝ) :=
  Measure.pi (coordLaw m μ)

instance : IsProbabilityMeasure (lossLaw m μ) := by
  unfold lossLaw
  infer_instance

/-- The losses in the support of the law: losses of the construction, with `|ℓ (Z i)| ≤ 1` and
`ℓ P = μ`. -/
def IsLawLoss (m : ℕ) (μ : ℝ) (x : Fin m × Fin 5 ⊕ Fin 2 → ℝ) : Prop :=
  IsShapedLoss x ∧ (∀ i, |x (.inl (i, 4))| ≤ 1) ∧ x (.inr 0) = μ

lemma ae_isLawLoss : ∀ᵐ x ∂lossLaw m μ, IsLawLoss m μ x := by
  have hcoord : ∀ (j : Fin m × Fin 5 ⊕ Fin 2) (p : ℝ → Prop), (∀ᵐ y ∂coordLaw m μ j, p y) →
      ∀ᵐ x ∂lossLaw m μ, p (x j) := fun j p h ↦ Measure.tendsto_eval_ae_ae.eventually h
  have hX := fun i : Fin m ↦ hcoord (.inl (i, 0)) (· = 0) (ae_dirac_eq_self 0)
  have hY1 := fun i : Fin m ↦ hcoord (.inl (i, 1)) (· = 1) (ae_dirac_eq_self 1)
  have hY2 := fun i : Fin m ↦ hcoord (.inl (i, 2)) (· = 1) (ae_dirac_eq_self 1)
  have hY3 := fun i : Fin m ↦ hcoord (.inl (i, 3)) (· = 1) (ae_dirac_eq_self 1)
  have hZ := fun i : Fin m ↦ hcoord (.inl (i, 4)) (fun y ↦ |y| ≤ 1) ae_abs_le_one_rademacher
  have hP := hcoord (.inr 0) (· = μ) (ae_dirac_eq_self μ)
  have hQ := hcoord (.inr 1) (· = 0) (ae_dirac_eq_self 0)
  filter_upwards [ae_all_iff.mpr hX, ae_all_iff.mpr hY1, ae_all_iff.mpr hY2, ae_all_iff.mpr hY3,
    ae_all_iff.mpr hZ, hP, hQ] with x hx hy1 hy2 hy3 hz hp hq
  exact ⟨⟨fun i ↦ ⟨hx i, hy1 i, hy2 i, hy3 i⟩, hq⟩, hz, hp⟩

/-- Under the law of the losses, every coordinate is in `[-1, 1]` if `|μ| ≤ 1`. -/
lemma ae_mem_Icc (hμ : |μ| ≤ 1) : ∀ᵐ x ∂lossLaw m μ, ∀ j, x j ∈ Icc (-1 : ℝ) 1 := by
  filter_upwards [ae_isLawLoss] with x hx
  obtain ⟨⟨hXY, hQ⟩, hZ, hP⟩ := hx
  have h : ∀ j, |x j| ≤ 1 := by
    rintro (⟨i, k⟩ | k)
    · obtain ⟨h0, h1, h2, h3⟩ := hXY i
      fin_cases k
      exacts [by simp [h0], by simp [h1], by simp [h2], by simp [h3], hZ i]
    · fin_cases k
      exacts [hP ▸ hμ, by simp [hQ]]
  exact fun j ↦ abs_le.mp (h j)

/-- Almost surely, every loss of the i.i.d. sequence is in the support of the law. -/
lemma ae_forall_isLawLoss :
    ∀ᵐ ℓ ∂(Measure.infinitePi fun _ : ℕ ↦ lossLaw m μ), ∀ t, IsLawLoss m μ (ℓ t) :=
  ae_all_iff.mpr fun t ↦ QuasiMeasurePreserving.ae
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ lossLaw m μ) t).quasiMeasurePreserving
    ae_isLawLoss

/-! ### The symmetry -/

/-- `-1` on the `Z`-coordinates and `1` elsewhere. -/
noncomputable def zSign : Fin m × Fin 5 ⊕ Fin 2 → ℝ :=
  Sum.elim (fun p ↦ if p.2 = 4 then -1 else 1) fun _ ↦ 1

lemma zSign_mul_self (j : Fin m × Fin 5 ⊕ Fin 2) : zSign j * zSign j = 1 := by
  rcases j with ⟨i, k⟩ | k
  · simp only [zSign, Sum.elim_inl]
    split_ifs <;> norm_num
  · simp [zSign]

lemma map_zSign_mul (j : Fin m × Fin 5 ⊕ Fin 2) :
    (coordLaw m μ j).map (fun x ↦ zSign j * x) = coordLaw m μ j := by
  match j with
  | .inl (i, 4) => exact map_neg_one_mul_rademacher
  | .inl (i, 0) => simp [zSign, Measure.map_id']
  | .inl (i, 1) => simp [zSign, Measure.map_id']
  | .inl (i, 2) => simp [zSign, Measure.map_id']
  | .inl (i, 3) => simp [zSign, Measure.map_id']
  | .inr 0 => simp [zSign, Measure.map_id']
  | .inr 1 => simp [zSign, Measure.map_id']

/-- Flip the signs of the `Z`-coordinates of the losses of the rounds in `R`. -/
noncomputable def flipZ (R : Finset ℕ) (ℓ : ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ) :
    ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ :=
  fun t j ↦ if t ∈ R then zSign j * ℓ t j else ℓ t j

lemma flipZ_flipZ (R : Finset ℕ) : Function.Involutive (flipZ (m := m) R) := by
  intro ℓ
  ext t j
  by_cases h : t ∈ R
  · simp only [flipZ, h, ite_true, ← mul_assoc, zSign_mul_self, one_mul]
  · simp [flipZ, h]

lemma measurable_flipCoord (b : Prop) [Decidable b] :
    Measurable fun (x : Fin m × Fin 5 ⊕ Fin 2 → ℝ) j ↦ if b then zSign j * x j else x j := by
  by_cases hb : b
  · simp only [hb, ite_true]
    exact measurable_pi_iff.mpr fun j ↦ (measurable_pi_apply j).const_mul _
  · simp only [hb, ite_false]
    exact measurable_id

lemma measurable_flipZ (R : Finset ℕ) : Measurable (flipZ (m := m) R) :=
  measurable_pi_iff.mpr fun t ↦ (measurable_flipCoord (t ∈ R)).comp (measurable_pi_apply t)

lemma map_lossLaw (b : Prop) [Decidable b] :
    (lossLaw m μ).map (fun x j ↦ if b then zSign j * x j else x j) = lossLaw m μ := by
  by_cases hb : b
  · simp only [hb, ite_true]
    have hmap := map_zSign_mul (m := m) (μ := μ)
    have : ∀ j, SigmaFinite ((coordLaw m μ j).map (fun x ↦ zSign j * x)) := fun j ↦ by
      rw [hmap j]
      infer_instance
    rw [lossLaw, Measure.pi_map_pi fun j ↦ (measurable_const_mul _).aemeasurable]
    simp_rw [hmap]
  · simp [hb, Measure.map_id']

/-- **The symmetry of the law of the losses**: flipping the signs of the `Z`-coordinates of the
rounds in `R` preserves the law of the i.i.d. sequence. -/
lemma measurePreserving_flipZ (R : Finset ℕ) :
    MeasurePreserving (flipZ R) (Measure.infinitePi fun _ : ℕ ↦ lossLaw m μ)
      (Measure.infinitePi fun _ : ℕ ↦ lossLaw m μ) := by
  refine ⟨measurable_flipZ R, ?_⟩
  have h := Measure.infinitePi_map_pi (fun _ : ℕ ↦ lossLaw m μ)
    (f := fun t (x : Fin m × Fin 5 ⊕ Fin 2 → ℝ) j ↦ if t ∈ R then zSign j * x j else x j)
    fun t ↦ measurable_flipCoord (t ∈ R)
  refine h.trans ?_
  simp_rw [map_lossLaw]

/-- The sign flip as a measurable equivalence. -/
noncomputable def flipZEquiv (R : Finset ℕ) :
    (ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ) ≃ᵐ (ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ) :=
  MeasurableEquiv.ofInvolutive (flipZ R) (flipZ_flipZ R) (measurable_flipZ R)

lemma integral_comp_flipZ (R : Finset ℕ) (f : (ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ) → ℝ) :
    ∫ ℓ, f (flipZ R ℓ) ∂(Measure.infinitePi fun _ : ℕ ↦ lossLaw m μ) =
      ∫ ℓ, f ℓ ∂(Measure.infinitePi fun _ : ℕ ↦ lossLaw m μ) :=
  MeasurePreserving.integral_comp' (f := flipZEquiv R) (measurePreserving_flipZ R) f

/-- **The median event** [SSKM26, Lemma 45], corrected (erratum E30): the sum of the
`Z`-coordinates of the losses of the first `n` rounds is nonpositive with probability at least
`1 / 2`. -/
lemma half_le_measureReal_sum_le_zero (n : ℕ) :
    1 / 2 ≤ (Measure.infinitePi fun _ : ℕ ↦ lossLaw m μ).real
      {ℓ | ∑ s ∈ Finset.range n, ∑ i, ℓ s (.inl (i, 4)) ≤ 0} := by
  set P := Measure.infinitePi fun _ : ℕ ↦ lossLaw m μ
  set G : (ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ) → ℝ :=
    fun ℓ ↦ ∑ s ∈ Finset.range n, ∑ i, ℓ s (.inl (i, 4))
  have hG : Measurable G := Finset.measurable_sum _ fun s _ ↦ Finset.measurable_sum _ fun i _ ↦
    (measurable_pi_apply _).comp (measurable_pi_apply s)
  have hflip : ∀ ℓ, G (flipZ (Finset.range n) ℓ) = -G ℓ := by
    intro ℓ
    simp only [G, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s hs ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    simp [flipZ, hs, zSign]
  set A := {ℓ | G ℓ ≤ 0}
  have hA : MeasurableSet A := measurableSet_le hG measurable_const
  have hpre : flipZ (Finset.range n) ⁻¹' A = {ℓ | 0 ≤ G ℓ} := by
    ext ℓ
    simp [A, hflip]
  have heq : P.real (flipZ (Finset.range n) ⁻¹' A) = P.real A := by
    simp only [measureReal_def]
    rw [(measurePreserving_flipZ (Finset.range n)).measure_preimage hA.nullMeasurableSet]
  have hunion : A ∪ flipZ (Finset.range n) ⁻¹' A = univ := by
    rw [hpre]
    ext ℓ
    simp only [A, mem_union, mem_ofPred_eq, mem_univ, iff_true]
    exact le_total _ _
  have h1 : 1 ≤ P.real A + P.real (flipZ (Finset.range n) ⁻¹' A) := by
    calc (1 : ℝ) = P.real (A ∪ flipZ (Finset.range n) ⁻¹' A) := by rw [hunion]; simp
      _ ≤ _ := measureReal_union_le _ _
  rw [heq] at h1
  linarith

/-- **A `Z`-coordinate of the loss of a round is centred given the other rounds**: if `φ` does not
change when the signs of the `Z`-coordinates of round `t` are flipped, then
`E[ℓ t (Z i) φ] = 0`. -/
lemma integral_mul_eq_zero (t : ℕ) (i : Fin m) {φ : (ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ) → ℝ}
    (hφ : ∀ ℓ, φ (flipZ {t} ℓ) = φ ℓ) :
    ∫ ℓ, ℓ t (.inl (i, 4)) * φ ℓ ∂(Measure.infinitePi fun _ : ℕ ↦ lossLaw m μ) = 0 := by
  have h := integral_comp_flipZ (μ := μ) {t} fun ℓ ↦ ℓ t (.inl (i, 4)) * φ ℓ
  have h1 : (fun ℓ ↦ flipZ {t} ℓ t (.inl (i, 4)) * φ (flipZ {t} ℓ)) =
      fun ℓ : ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ ↦ -(ℓ t (.inl (i, 4)) * φ ℓ) := by
    funext ℓ
    simp [flipZ, zSign, hφ]
  rw [h1, integral_neg] at h
  linarith

/-! ### The expected regret -/

/-- The loss of a point of the curve, for a loss in the support of the law. -/
lemma sum_mul_curve {x : Fin m × Fin 5 ⊕ Fin 2 → ℝ} (hx : IsLawLoss m μ x) (E q : ℝ) :
    ∑ j, x j * curve m E q j =
      3 * m * curveY m E q + μ * (2 / (5 * m + 2) - q) +
        ∑ i, x (.inl (i, 4)) * (2 / (5 * m + 2) - q) := by
  obtain ⟨⟨hXY, hQ⟩, -, hP⟩ := hx
  rw [sum_coord]
  have hi : ∀ i, x (.inl (i, 0)) * curve m E q (.inl (i, 0)) +
      x (.inl (i, 1)) * curve m E q (.inl (i, 1)) + x (.inl (i, 2)) * curve m E q (.inl (i, 2)) +
      x (.inl (i, 3)) * curve m E q (.inl (i, 3)) + x (.inl (i, 4)) * curve m E q (.inl (i, 4)) =
      3 * curveY m E q + x (.inl (i, 4)) * (2 / (5 * m + 2) - q) := by
    intro i
    obtain ⟨h0, h1, h2, h3⟩ := hXY i
    simp only [curve_X, curve_Y1, curve_Y2, curve_Y3, curve_Z, h0, h1, h2, h3]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ hi i, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, curve_P, curve_Q, hP, hQ]
  ring

variable {η ε : ℝ} {τ : ℕ}

lemma integrable_of_abs_le {f : (ℕ → Fin m × Fin 5 ⊕ Fin 2 → ℝ) → ℝ} (hf : Measurable f) (C : ℝ)
    (h : ∀ᵐ ℓ ∂(Measure.infinitePi fun _ : ℕ ↦ lossLaw m μ), |f ℓ| ≤ C) :
    Integrable f (Measure.infinitePi fun _ : ℕ ↦ lossLaw m μ) :=
  Integrable.of_bound hf.aestronglyMeasurable C (by simpa only [Real.norm_eq_abs] using h)

lemma measurable_curveY_trajQ (t : ℕ) (E : ℝ) :
    Measurable fun ℓ ↦ curveY m E (trajQ m η ε τ t ℓ) := by
  unfold curveY
  exact ((measurable_trajQ t).const_add _).div_const _

lemma integrable_curveY_trajQ (t : ℕ) {E : ℝ} (hE : 0 < E) :
    Integrable (fun ℓ ↦ curveY m E (trajQ m η ε τ t ℓ))
      (Measure.infinitePi fun _ : ℕ ↦ lossLaw m μ) := by
  refine integrable_of_abs_le (measurable_curveY_trajQ t E) 1 (Filter.Eventually.of_forall
    fun ℓ ↦ ?_)
  have hq := trajQ_mem (η := η) (ε := ε) (τ := τ) t ℓ
  have hd : (2 : ℝ) ≤ 5 * m + 2 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hy := curveY_pos (m := m) hE hq.1
  rw [abs_of_pos hy, curveY, div_le_one (by linarith)]
  have : 3 / (5 * m + 2 : ℝ) ≤ 3 / 2 := by gcongr
  have : 2 / (5 * m + 2 : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hd
  linarith [hq.2]

lemma integrable_sub_trajQ (t : ℕ) :
    Integrable (fun ℓ ↦ 2 / (5 * m + 2) - trajQ m η ε τ t ℓ)
      (Measure.infinitePi fun _ : ℕ ↦ lossLaw m μ) := by
  refine integrable_of_abs_le ((measurable_trajQ t).const_sub _) (2 / (5 * m + 2))
    (Filter.Eventually.of_forall fun ℓ ↦ ?_)
  have hq := trajQ_mem (η := η) (ε := ε) (τ := τ) t ℓ
  rw [abs_le]
  constructor <;> linarith [hq.1, hq.2]

lemma integrable_mul_sub_trajQ (t : ℕ) (i : Fin m) :
    Integrable (fun ℓ ↦ ℓ t (.inl (i, 4)) * (2 / (5 * m + 2) - trajQ m η ε τ t ℓ))
      (Measure.infinitePi fun _ : ℕ ↦ lossLaw m μ) := by
  refine integrable_of_abs_le (by fun_prop) (2 / (5 * m + 2)) ?_
  filter_upwards [ae_forall_isLawLoss] with ℓ hℓ
  have hq := trajQ_mem (η := η) (ε := ε) (τ := τ) t ℓ
  have hz : |2 / (5 * m + 2) - trajQ m η ε τ t ℓ| ≤ 2 / (5 * m + 2) := by
    rw [abs_le]
    constructor <;> linarith [hq.1, hq.2]
  rw [abs_mul]
  calc |ℓ t (.inl (i, 4))| * |2 / (5 * m + 2) - trajQ m η ε τ t ℓ| ≤ 1 * (2 / (5 * m + 2)) := by
        gcongr
        exact (hℓ t).2.1 i
    _ = 2 / (5 * m + 2) := one_mul _

/-- **The expected regret of the trajectory** [SSKM26, proof of Theorem 49], corrected (erratum
E34): each play depends on the past losses only, so the `Z`-coordinates of the loss of its round
are centred given it, and the expected regret against the comparator is
`∑_{t<T} (3 m E[y_t] + μ E[2 / d - q_t])`. -/
lemma integral_regret_eq (T : ℕ) :
    ∫ ℓ, regret (fun t w ↦ ∑ j, ℓ t j * w j) (fun t ↦ traj m η ε τ t ℓ) (comparator m) T
        ∂(Measure.infinitePi fun _ : ℕ ↦ lossLaw m μ) =
      ∑ t ∈ Finset.range T,
        (3 * m * ∫ ℓ, curveY m (exp (η * t)) (trajQ m η ε τ t ℓ)
            ∂(Measure.infinitePi fun _ : ℕ ↦ lossLaw m μ) +
          μ * ∫ ℓ, (2 / (5 * m + 2) - trajQ m η ε τ t ℓ)
            ∂(Measure.infinitePi fun _ : ℕ ↦ lossLaw m μ)) := by
  set P := Measure.infinitePi fun _ : ℕ ↦ lossLaw m μ
  have hae : (fun ℓ ↦ regret (fun t w ↦ ∑ j, ℓ t j * w j) (fun t ↦ traj m η ε τ t ℓ)
      (comparator m) T) =ᵐ[P] fun ℓ ↦ ∑ t ∈ Finset.range T,
        (3 * m * curveY m (exp (η * t)) (trajQ m η ε τ t ℓ) +
          μ * (2 / (5 * m + 2) - trajQ m η ε τ t ℓ) +
          ∑ i, ℓ t (.inl (i, 4)) * (2 / (5 * m + 2) - trajQ m η ε τ t ℓ)) := by
    filter_upwards [ae_forall_isLawLoss] with ℓ hℓ
    rw [regret_def]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [traj, sum_mul_curve (hℓ t), sum_mul_comparator_eq_zero (hℓ t).1, sub_zero]
  have hI1 : ∀ t : ℕ, Integrable (fun ℓ ↦ 3 * m * curveY m (exp (η * t)) (trajQ m η ε τ t ℓ)) P :=
    fun t ↦ (integrable_curveY_trajQ t (exp_pos _)).const_mul _
  have hI2 : ∀ t : ℕ, Integrable (fun ℓ ↦ μ * (2 / (5 * m + 2) - trajQ m η ε τ t ℓ)) P :=
    fun t ↦ (integrable_sub_trajQ t).const_mul _
  have hI3 : ∀ t : ℕ, Integrable
      (fun ℓ ↦ ∑ i, ℓ t (.inl (i, 4)) * (2 / (5 * m + 2) - trajQ m η ε τ t ℓ)) P :=
    fun t ↦ integrable_finsetSum _ fun i _ ↦ integrable_mul_sub_trajQ t i
  have hI12 : ∀ t : ℕ, Integrable (fun ℓ ↦ 3 * m * curveY m (exp (η * t)) (trajQ m η ε τ t ℓ) +
      μ * (2 / (5 * m + 2) - trajQ m η ε τ t ℓ)) P := fun t ↦ (hI1 t).add (hI2 t)
  rw [integral_congr_ae hae, integral_finsetSum _ fun t _ ↦ ?_]
  swap
  · exact (hI12 t).add (hI3 t)
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [integral_add (hI12 t) (hI3 t), integral_add (hI1 t) (hI2 t), integral_const_mul,
    integral_const_mul, integral_finsetSum _ fun i _ ↦ integrable_mul_sub_trajQ t i]
  have hzero : ∀ i : Fin m, ∫ ℓ, ℓ t (.inl (i, 4)) * (2 / (5 * m + 2) - trajQ m η ε τ t ℓ) ∂P = 0 :=
    fun i ↦ integral_mul_eq_zero t i fun ℓ ↦ by
      rw [trajQ_congr t fun s hs ↦ ?_]
      ext j
      simp [flipZ, hs.ne]
  rw [add_eq_left]
  exact Finset.sum_eq_zero fun i _ ↦ hzero i

/-- **The lower bound on the expected regret** [SSKM26, Theorem 49], corrected, under the
parameter constraints of the construction: the expected regret against the comparator is at least
`T μ / (2 d)`, and at least `3 m / (2 d η) + T μ / (2 d)` if `η T ≥ 1`. -/
lemma le_integral_regret (hη : 0 < η) (hηd : η * (5 * m + 2) ≤ 1) (hm7 : 7 ≤ m)
    (hε : 0 < ε) (hε3 : ε ≤ 1 / 3) (hm : 16 * log (1 / ε) ≤ m) (hτ : 3 ≤ η * τ)
    (hτ' : η * τ ≤ 7 / 2) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) (T : ℕ) :
    T * μ / (2 * (5 * m + 2)) ≤
        ∫ ℓ, regret (fun t w ↦ ∑ j, ℓ t j * w j) (fun t ↦ traj m η ε τ t ℓ) (comparator m) T
          ∂(Measure.infinitePi fun _ : ℕ ↦ lossLaw m μ) ∧
      (1 ≤ η * T → 3 * m / (2 * (5 * m + 2) * η) + T * μ / (2 * (5 * m + 2)) ≤
        ∫ ℓ, regret (fun t w ↦ ∑ j, ℓ t j * w j) (fun t ↦ traj m η ε τ t ℓ) (comparator m) T
          ∂(Measure.infinitePi fun _ : ℕ ↦ lossLaw m μ)) := by
  set P := Measure.infinitePi fun _ : ℕ ↦ lossLaw m μ
  set d : ℝ := 5 * m + 2 with hd_def
  have hd : 0 < d := by positivity
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm7
  -- the `Z`/`P` part: `E[2 / d - q_t] ≥ 1 / (2 d)`
  have hz : ∀ t, 1 / (2 * d) ≤ ∫ ℓ, (2 / d - trajQ m η ε τ t ℓ) ∂P := by
    intro t
    have hprob : 1 / 2 ≤ P.real {ℓ | d⁻¹ ≤ 2 / d - trajQ m η ε τ t ℓ} := by
      refine (half_le_measureReal_sum_le_zero (m := m) (μ := μ) (min t τ)).trans ?_
      simp only [measureReal_def]
      refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
      filter_upwards [ae_forall_isLawLoss] with ℓ hℓ hG
      have hS : ∀ s, |lossZP (ℓ s)| ≤ m + 1 := by
        intro s
        have hsum : |∑ i, ℓ s (.inl (i, 4))| ≤ m := by
          calc |∑ i, ℓ s (.inl (i, 4))| ≤ ∑ i : Fin m, |ℓ s (.inl (i, 4))| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _i : Fin m, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ (hℓ s).2.1 i
            _ = m := by simp
        rw [lossZP, (hℓ s).2.2]
        calc |∑ i, ℓ s (.inl (i, 4)) + μ| ≤ |∑ i, ℓ s (.inl (i, 4))| + |μ| := abs_add_le _ _
          _ ≤ m + 1 := by rw [abs_of_nonneg hμ]; linarith
      have hGle : ∑ s ∈ Finset.range (min t τ), lossZP (ℓ s) ≤ (min t τ : ℕ) * μ := by
        have : ∑ s ∈ Finset.range (min t τ), lossZP (ℓ s) =
            ∑ s ∈ Finset.range (min t τ), ∑ i, ℓ s (.inl (i, 4)) + (min t τ : ℕ) * μ := by
          rw [Finset.sum_congr rfl fun s _ ↦ show lossZP (ℓ s) = ∑ i, ℓ s (.inl (i, 4)) + μ by
            rw [lossZP, (hℓ s).2.2], Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul]
        rw [this]
        have hG' : ∑ s ∈ Finset.range (min t τ), ∑ i, ℓ s (.inl (i, 4)) ≤ 0 := hG
        linarith
      have := trajQ_le_inv hη hηd hm7 hε hε3 hm hτ hτ' hμ1 hS t (by exact_mod_cast hGle)
      rw [← hd_def] at this
      change d⁻¹ ≤ 2 / d - trajQ m η ε τ t ℓ
      have h2 : 2 / d = 2 * d⁻¹ := by ring
      linarith
    have hnonneg : 0 ≤ᵐ[P] fun ℓ ↦ 2 / d - trajQ m η ε τ t ℓ :=
      Filter.Eventually.of_forall fun ℓ ↦ by
        have hq := (trajQ_mem (m := m) (η := η) (ε := ε) (τ := τ) t ℓ).2
        rw [← hd_def] at hq
        change 0 ≤ 2 / d - trajQ m η ε τ t ℓ
        linarith
    have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg (integrable_sub_trajQ t) d⁻¹
    calc 1 / (2 * d) = d⁻¹ * (1 / 2) := by field_simp
      _ ≤ d⁻¹ * P.real {ℓ | d⁻¹ ≤ 2 / d - trajQ m η ε τ t ℓ} := by gcongr
      _ ≤ _ := hmarkov
  -- the `Y` part: `E[y_t] ≥ (3 / d) / (e^{η t} + 3)`
  have hy : ∀ t : ℕ, 3 / d / (exp (η * t) + 3) ≤
      ∫ ℓ, curveY m (exp (η * t)) (trajQ m η ε τ t ℓ) ∂P := by
    intro t
    calc 3 / d / (exp (η * t) + 3) = ∫ _ℓ, 3 / d / (exp (η * t) + 3) ∂P := by simp
      _ ≤ _ := integral_mono (integrable_const _) (integrable_curveY_trajQ t (exp_pos _))
          fun ℓ ↦ curveY_ge (exp_pos _) (trajQ_mem t ℓ).1.le
  have hy0 : ∀ t : ℕ, 0 ≤ ∫ ℓ, curveY m (exp (η * t)) (trajQ m η ε τ t ℓ) ∂P :=
    fun t ↦ (by positivity : (0 : ℝ) ≤ 3 / d / (exp (η * t) + 3)).trans (hy t)
  rw [integral_regret_eq]
  have hlow : ∀ t ∈ Finset.range T, μ * (1 / (2 * d)) ≤
      3 * m * ∫ ℓ, curveY m (exp (η * t)) (trajQ m η ε τ t ℓ) ∂P +
        μ * ∫ ℓ, (2 / d - trajQ m η ε τ t ℓ) ∂P := by
    intro t _
    have := mul_le_mul_of_nonneg_left (hz t) hμ
    have := mul_nonneg (by positivity : (0 : ℝ) ≤ 3 * m) (hy0 t)
    linarith
  have hsum : T * μ / (2 * d) ≤ ∑ t ∈ Finset.range T,
      (3 * m * ∫ ℓ, curveY m (exp (η * t)) (trajQ m η ε τ t ℓ) ∂P +
        μ * ∫ ℓ, (2 / d - trajQ m η ε τ t ℓ) ∂P) := by
    calc T * μ / (2 * d) = ∑ _t ∈ Finset.range T, μ * (1 / (2 * d)) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
      _ ≤ _ := Finset.sum_le_sum hlow
  refine ⟨hsum, fun hηT ↦ ?_⟩
  -- the rounds `t < K = min T (⌊1 / η⌋ + 1)` have `η t ≤ 1`, so `E[y_t] ≥ 1 / (2 d)`
  set K := min T (⌊1 / η⌋₊ + 1)
  have hK : 1 / η ≤ K := by
    rcases min_choice T (⌊1 / η⌋₊ + 1) with h | h
    · rw [show K = T from h, div_le_iff₀ hη]
      linarith
    · rw [show K = ⌊1 / η⌋₊ + 1 from h]
      push_cast
      exact (Nat.lt_floor_add_one _).le
  have hyK : ∀ t ∈ Finset.range K, 3 * m * (1 / (2 * d)) ≤
      3 * m * ∫ ℓ, curveY m (exp (η * t)) (trajQ m η ε τ t ℓ) ∂P := by
    intro t ht
    have ht' : (t : ℝ) ≤ 1 / η := by
      have : t ≤ ⌊1 / η⌋₊ := by
        have := Finset.mem_range.mp ht
        omega
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le (by positivity))
    have hηt : η * t ≤ 1 := by rwa [le_div_iff₀ hη, mul_comm] at ht'
    have hexp : exp (η * t) ≤ 3 := by
      have := exp_le_exp.mpr hηt
      linarith [exp_one_lt_d9]
    gcongr
    refine le_trans ?_ (hy t)
    rw [div_div, one_div]
    rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    nlinarith
  have hY : 3 * m / (2 * d * η) ≤ ∑ t ∈ Finset.range T,
      3 * m * ∫ ℓ, curveY m (exp (η * t)) (trajQ m η ε τ t ℓ) ∂P := by
    calc 3 * m / (2 * d * η) = 3 * m * (1 / (2 * d)) * (1 / η) := by field_simp
      _ ≤ 3 * m * (1 / (2 * d)) * K := by gcongr
      _ = ∑ _t ∈ Finset.range K, 3 * m * (1 / (2 * d)) := by simp [mul_comm]
      _ ≤ ∑ t ∈ Finset.range K, 3 * m * ∫ ℓ, curveY m (exp (η * t)) (trajQ m η ε τ t ℓ) ∂P :=
          Finset.sum_le_sum hyK
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (min_le_left _ _))
          fun t _ _ ↦ mul_nonneg (by positivity) (hy0 t)
  have hZ : T * μ / (2 * d) ≤ ∑ t ∈ Finset.range T, μ * ∫ ℓ, (2 / d - trajQ m η ε τ t ℓ) ∂P := by
    calc T * μ / (2 * d) = ∑ _t ∈ Finset.range T, μ * (1 / (2 * d)) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
      _ ≤ _ := Finset.sum_le_sum fun t _ ↦ mul_le_mul_of_nonneg_left (hz t) hμ
  rw [Finset.sum_add_distrib]
  linarith

end Schlisselberg2026Hidden.PolytopeLower
