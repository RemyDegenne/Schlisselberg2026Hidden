/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent.Smooth

/-!
# Theorem 2 of [SSKM26]: approximate mirror descent with a smooth regularizer

Let `K` be a convex set of diameter at most `D` in a real normed space, and let the regularizer
`R` be `1`-strongly convex on `K` and `β`-smooth on `K` (its derivative is `β`-Lipschitz from the
norm to the dual norm). For losses of dual norm at most `1` and `ε ≤ D² / 2`, every
`ε`-approximate trajectory of mirror descent has regret at most
`D_R(u, w₁) / η + η T / 2 + T D √(2 β ε) / η` against every `u ∈ K`.

The paper states the bound as `O(D_R(u, w₁) / η + T η + T D √(β ε) / η)`; the constants above are
those of its proof. The proof is the standard analysis of mirror descent, with the first-order
optimality condition of each step replaced by the approximate one of an `ε`-minimizer of a
`β`-smooth function, `⟨∇f(ŵ), w - ŵ⟩ ≥ -D √(2 β ε)` (Lemma 22 of [SSKM26],
`LMLExplore.neg_mul_sqrt_le_apply_sub_of_le_add`). It is the case `m = 1`, `ε t = ε` and
`‖y t‖ ≤ 1` of `LMLExplore.OnlineLearning.approxMirrorDescent_sum_apply_sub_le`.

## Main statements

* `Schlisselberg2026Hidden.approxMirrorDescent_regret_le_of_smooth`: [SSKM26, Theorem 2].

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore.OnlineLearning

namespace Schlisselberg2026Hidden

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Approximate mirror descent with a smooth regularizer** [SSKM26, Theorem 2]. Let `K` be a
convex set with `‖x - x'‖ ≤ D` for all `x, x' ∈ K`, and let `R` have a derivative `R' x` within
`K` at every `x ∈ K`, be `1`-strongly convex on `K`, and be `β`-smooth on `K`:
`‖R' x - R' x'‖ ≤ β ‖x - x'‖`. Let `η > 0` and `ε ≤ D² / 2`. For losses `y t` of dual norm at most
`1`, if each `a (t + 1)`, `t < T`, is an `ε`-approximate mirror descent step on `K` from `a t`
with potential `R` and learning rate `η`, then for every `u ∈ K` the regret after `T` rounds is
at most `D_R(u, a 0) / η + η T / 2 + T D √(2 β ε) / η`.

The paper states this for `K ⊆ ℝ^d` and with `O(·)`; the constants are those of its proof. -/
theorem approxMirrorDescent_regret_le_of_smooth {K : Set E} (hK : Convex ℝ K) {D : ℝ}
    (hD : ∀ x ∈ K, ∀ x' ∈ K, ‖x - x'‖ ≤ D) {R : E → ℝ} (R' : E → E →L[ℝ] ℝ)
    (hR' : ∀ x ∈ K, HasFDerivWithinAt R (R' x) K x) (hR : StrongConvexOn K 1 R) {β : ℝ}
    (hβ : ∀ x ∈ K, ∀ x' ∈ K, ‖R' x - R' x'‖ ≤ β * ‖x - x'‖) {η ε : ℝ} (hη : 0 < η)
    (hεD : ε ≤ D ^ 2 / 2) {T : ℕ} (y : ℕ → E →L[ℝ] ℝ) (hy : ∀ t < T, ‖y t‖ ≤ 1) (a : ℕ → E)
    (ha0 : a 0 ∈ K)
    (ha : ∀ t < T, IsApproxMirrorDescentStep K R η (y t) (a t) (R' (a t)) ε (a (t + 1)))
    {u : E} (hu : u ∈ K) :
    regret (fun t b ↦ y t b) a u T ≤
      bregDiv R u (a 0) (R' (a 0)) / η + η * T / 2 + T * D * √(2 * β * ε) / η := by
  have h := approxMirrorDescent_sum_apply_sub_le hK hR' hR one_pos hβ hD hη y (fun _ ↦ ε)
    (fun _ _ ↦ by linarith) a ha0 ha hu
  have h_sq : ∑ t ∈ Finset.range T, ‖y t‖ ^ 2 ≤ T := by
    refine (Finset.sum_le_sum (g := fun _ ↦ (1 : ℝ)) fun t ht ↦ ?_).trans_eq (by simp)
    exact pow_le_one₀ (norm_nonneg _) (hy t (Finset.mem_range.mp ht))
  have h_const : ∑ t ∈ Finset.range T, √(2 * β * ε) = T * √(2 * β * ε) := by simp
  have h_stab : η / (2 * 1) * ∑ t ∈ Finset.range T, ‖y t‖ ^ 2 ≤ η * T / 2 := by
    have := mul_le_mul_of_nonneg_left h_sq hη.le
    linarith
  simp only [h_const] at h
  rw [regret_eq_sum_apply_sub (fun t ↦ y t)]
  linarith [show D * (T * √(2 * β * ε)) / η = T * D * √(2 * β * ε) / η by ring]

end Schlisselberg2026Hidden
