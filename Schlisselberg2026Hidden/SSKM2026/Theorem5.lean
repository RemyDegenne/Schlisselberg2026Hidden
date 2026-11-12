/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.ForLMLExplore.OnlineLearning.ApproxMirrorDescent
public import Schlisselberg2026Hidden.SSKM2026.Lemma15
public import LMLExplore.Analysis.Convex.NegEntropy

/-!
# Theorem 5 of [SSKM26]: exponentially small errors suffice for the negative entropy

On the simplex with the negative entropy, for losses in `[0, 1]^d`, `η ≤ 1/16`, the uniform initial
point and `ε ≤ e^{-η T / 2} min (η⁴, 1/T²) / (100 d)`, every `ε`-approximate trajectory of mirror
descent has regret at most `log d / η + η T`. Together with Theorem 4 of [SSKM26], which gives
linear regret for `ε ≥ 4 η e^{-η T / 3}`, this shows that the negative entropy tolerates only
exponentially small errors.

Losses in `[0, 1]^d` are `T / 2`-balanced, so this is Lemma 15 of [SSKM26] with `A = T / 2`.

The paper states the theorem for losses in `[-1, 1]^d`, where it is false; with the threshold
`e^{-η T / 2} min (η⁴, T^{-2}) / (6 d)`, the comparator term `D_R(w, w₁) / η`, `O(η T)`, `T ≥ 3`
and no initial point (`notes/paper-errata.md`).

## Main statements

* `Schlisselberg2026Hidden.approxMirrorDescent_regret_le_negEntropy`: [SSKM26, Theorem 5],
  corrected.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*}

/-- **Losses in `[0, 1]^d` are `T / 2`-balanced** [SSKM26, proof of Theorem 5]. For losses with
coordinates in `[0, 1]` over `T` rounds and a best arm `i*`, the cumulative loss of `i*` over the
rounds `s ≤ r < t` exceeds that of any arm `i` by at most `T / 2`: by at most `t - s`, and by at
most `s + (T - t)` since `i*` is a best arm over the whole horizon. For losses in `[-1, 1]^d` the
best bound is `T`. -/
lemma sum_Ico_sub_le_half_of_mem_Icc {T : ℕ} {ℓ : ℕ → α → ℝ}
    (hℓ : ∀ t < T, ∀ i, ℓ t i ∈ Set.Icc 0 1) {iStar : α}
    (hbest : ∀ i, ∑ t ∈ range T, ℓ t iStar ≤ ∑ t ∈ range T, ℓ t i) {s t : ℕ}
    (hst : s ≤ t) (htT : t ≤ T) (i : α) :
    ∑ r ∈ Ico s t, (ℓ r iStar - ℓ r i) ≤ T / 2 := by
  have h_le (r : ℕ) (hr : r < T) : ℓ r iStar - ℓ r i ≤ 1 := by
    linarith [(hℓ r hr iStar).2, (hℓ r hr i).1]
  have h_ge (r : ℕ) (hr : r < T) : -1 ≤ ℓ r iStar - ℓ r i := by
    linarith [(hℓ r hr i).2, (hℓ r hr iStar).1]
  -- at most the length `t - s` of the interval
  have h1 : ∑ r ∈ Ico s t, (ℓ r iStar - ℓ r i) ≤ (t : ℝ) - s := by
    calc ∑ r ∈ Ico s t, (ℓ r iStar - ℓ r i) ≤ ∑ r ∈ Ico s t, (1 : ℝ) :=
          sum_le_sum fun r hr ↦ h_le r ((mem_Ico.1 hr).2.trans_le htT)
      _ = (t : ℝ) - s := by rw [sum_const, Nat.card_Ico, nsmul_one, Nat.cast_sub hst]
  -- at most the length `s + (T - t)` of the complement
  have h2 : ∑ r ∈ Ico s t, (ℓ r iStar - ℓ r i) ≤ s + ((T : ℝ) - t) := by
    have h_split : ∑ r ∈ range T, (ℓ r iStar - ℓ r i) = ∑ r ∈ range s, (ℓ r iStar - ℓ r i) +
        ∑ r ∈ Ico s t, (ℓ r iStar - ℓ r i) + ∑ r ∈ Ico t T, (ℓ r iStar - ℓ r i) := by
      rw [sum_range_add_sum_Ico _ hst, sum_range_add_sum_Ico _ htT]
    have h_tot : ∑ r ∈ range T, (ℓ r iStar - ℓ r i) ≤ 0 := by
      rw [sum_sub_distrib]
      linarith [hbest i]
    have h_pre : -(s : ℝ) ≤ ∑ r ∈ range s, (ℓ r iStar - ℓ r i) := by
      calc -(s : ℝ) = ∑ r ∈ range s, (-1 : ℝ) := by simp
        _ ≤ _ := sum_le_sum fun r hr ↦ h_ge r ((mem_range.1 hr).trans_le (hst.trans htT))
    have h_post : -((T : ℝ) - t) ≤ ∑ r ∈ Ico t T, (ℓ r iStar - ℓ r i) := by
      calc -((T : ℝ) - t) = ∑ r ∈ Ico t T, (-1 : ℝ) := by
            rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub htT]
            ring
        _ ≤ _ := sum_le_sum fun r hr ↦ h_ge r (mem_Ico.1 hr).2
    linarith
  linarith

variable [Fintype α]

/-- **Exponentially small errors suffice for the negative entropy** [SSKM26, Theorem 5], for
losses in `[0, 1]^d` and with corrected constants. Let `0 < η ≤ 1/16`, let the losses `ℓ t` have
coordinates in `[0, 1]`, and let `ε ≤ e^{-η T / 2} min (η⁴, 1/T²) / (100 d)`, with `d` the number
of arms. Then every `ε`-approximate trajectory `a` of mirror descent on the simplex with the
negative entropy and learning rate `η`, started at the uniform point and with positive
coordinates, has regret at most `log d / η + η T` against every point of the simplex. -/
theorem approxMirrorDescent_regret_le_negEntropy {η ε : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 16)
    {T : ℕ} (ℓ : ℕ → α → ℝ) (hℓ : ∀ t < T, ∀ i, ℓ t i ∈ Set.Icc 0 1)
    (hε : ε ≤ exp (-(η * T / 2)) * min (η ^ 4) (1 / (T : ℝ) ^ 2) / (100 * Fintype.card α))
    (a : ℕ → α → ℝ) (ha0 : a 0 = fun _ ↦ (Fintype.card α : ℝ)⁻¹)
    (hpos : ∀ t ≤ T, ∀ i, 0 < a t i)
    (ha : ∀ t < T, IsApproxMirrorDescentStep (simplex α) negEntropy η
      (∑ i, ℓ t i • ContinuousLinearMap.proj i) (a t)
      (∑ i, log (a t i) • ContinuousLinearMap.proj i) ε (a (t + 1)))
    {u : α → ℝ} (hu : u ∈ simplex α) :
    regret (fun t w ↦ ∑ i, ℓ t i * w i) a u T ≤ log (Fintype.card α) / η + η * T := by
  have : Nonempty α := nonempty_of_mem_simplex hu
  obtain ⟨iStar, -, hbest⟩ :=
    exists_min_image univ (fun i ↦ ∑ t ∈ range T, ℓ t i) univ_nonempty
  refine approxMirrorDescent_regret_le_negEntropy_of_balanced hη hη' ℓ
    (fun t ht i ↦ abs_le.2 ⟨by linarith [(hℓ t ht i).1], (hℓ t ht i).2⟩) iStar
    (fun i ↦ hbest i (mem_univ i))
    (fun s t hst htT i ↦ sum_Ico_sub_le_half_of_mem_Icc hℓ (fun i ↦ hbest i (mem_univ i)) hst htT i)
    ?_ a ha0 hpos ha hu
  rwa [← mul_div_assoc]

end Schlisselberg2026Hidden
