/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent
public import LMLExplore.Analysis.Convex.NegEntropy
public import Mathlib.Probability.ProductMeasure

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
  sorry

end Schlisselberg2026Hidden
