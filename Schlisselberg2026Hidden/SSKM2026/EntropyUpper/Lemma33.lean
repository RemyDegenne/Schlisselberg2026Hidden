/-
Copyright (c) 2026 Remy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Degenne
-/
module

public import Schlisselberg2026Hidden.SSKM2026.EntropyUpper.Lemma22

/-!
# Lemma 33 of [SSKM26] for the negative entropy: the balance of an approximate trajectory

For a trajectory `a` of mirror descent on the simplex with the negative entropy, the balance of
the arms `j` and `i` between the rounds `s` and `t` is
`B = (log (a s j) - log (a t j)) + (log (a t i) - log (a s i))` [SSKM26, Definition 32], the
derivative of the negative entropy being `log` up to a constant. For exact steps it is
`η (L_{[s,t)}(j) - L_{[s,t)}(i))`, with `L_{[s,t)}` the cumulative loss over the rounds
`s ≤ r < t`. For `ε`-approximate steps whose iterates keep the weights of `i` and `j` above `ψ`,
it exceeds this value by at most `1` when `ε ≤ ψ / (8 T²)`.

Each round costs at most `ε / v + v (1 / a (r + 1) j + 1 / a (r + 1) i)` for every
`0 < v ≤ a (r + 1) i`: this is the approximate first-order condition (Lemma 22 of [SSKM26]) in
the direction that moves the weight of `i` onto `j`. With `v = ψ / (4 T)` the cost is at most
`1 / T`.

The paper's Lemma 33 bounds the excess by `(t - s) √(ε / ψ)`, as a consequence of its Lemma 11
for `v = e_{i*} - e_i`; but `‖e_{i*} - e_i‖₁ = 2`, and the bound is false
(`notes/paper-errata.md`). Only the rounds `s < r ≤ t` need the lower bound `ψ`.

## Main statements

* `Schlisselberg2026Hidden.log_sub_log_add_le_of_isApproxMirrorDescentStep_negEntropy`: the
  balance of one approximate step.
* `Schlisselberg2026Hidden.log_sub_log_add_le_sum_add_one`: [SSKM26, Lemma 33], corrected, for
  the negative entropy.

## References

* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

@[expose] public section

open LMLExplore LMLExplore.OnlineLearning Finset Real

namespace Schlisselberg2026Hidden

variable {α : Type*} [Fintype α] {η ε : ℝ}

/-- **The balance of one approximate step.** If `w'` is an `ε`-approximate step of mirror
descent on the simplex with the negative entropy from `w`, both with positive coordinates, then
for arms `i ≠ j` and `0 < v ≤ w' i`,
`(log (w j) - log (w' j)) + (log (w' i) - log (w i)) ≤
  η (ℓ j - ℓ i) + ε / v + v (1 / w' j + 1 / w' i)`. -/
lemma log_sub_log_add_le_of_isApproxMirrorDescentStep_negEntropy {ℓ w w' : α → ℝ}
    (hw : ∀ k, 0 < w k) (hw' : ∀ k, 0 < w' k)
    (h : IsApproxMirrorDescentStep (simplex α) negEntropy η
      (∑ i, ℓ i • ContinuousLinearMap.proj i) w (∑ i, log (w i) • ContinuousLinearMap.proj i) ε w')
    {i j : α} (hij : i ≠ j) {v : ℝ} (hv : 0 < v) (hvi : v ≤ w' i) :
    log (w j) - log (w' j) + (log (w' i) - log (w i)) ≤
      η * (ℓ j - ℓ i) + ε / v + v * (1 / w' j + 1 / w' i) := by
  classical
  have hwi := hw' i
  have hwj := hw' j
  -- move the weight of `i` onto `j`
  set h' : α → ℝ := fun k ↦ if k = j then w' i else if k = i then -w' i else 0 with hh'
  have hh'j : h' j = w' i := by simp [hh']
  have hh'i : h' i = -w' i := by simp [hh', hij]
  have hh'0 (k : α) (hk : k ≠ j ∧ k ≠ i) : h' k = 0 := by simp [hh', hk.1, hk.2]
  have hmem : w' + h' ∈ simplex α := by
    refine mem_simplex_iff.2 ⟨fun k ↦ ?_, ?_⟩
    · simp only [Pi.add_apply]
      by_cases hkj : k = j
      · rw [hkj, hh'j]
        positivity
      by_cases hki : k = i
      · rw [hki, hh'i, add_neg_cancel]
      rw [hh'0 k ⟨hkj, hki⟩, add_zero]
      exact (hw' k).le
    · simp only [Pi.add_apply, sum_add_distrib, (mem_simplex_iff.1 h.mem).2]
      rw [Fintype.sum_eq_add j i hij.symm hh'0, hh'j, hh'i]
      ring
  have hu : 0 < v / w' i := div_pos hv hwi
  have hu1 : v / w' i ≤ 1 := (div_le_one hwi).2 hvi
  have h_fo := neg_div_sub_le_of_isApproxMirrorDescentStep_negEntropy hw hw' h hmem hu hu1
  rw [Fintype.sum_eq_add j i hij.symm (fun k hk ↦ by rw [hh'0 k hk]; simp),
    Fintype.sum_eq_add j i hij.symm (fun k hk ↦ by rw [hh'0 k hk, mul_zero]), hh'j, hh'i] at h_fo
  -- divide by `w' i`
  have e1 : -ε / (v / w' i) = -(w' i * (ε / v)) := by
    field_simp
  have e2 : v / w' i * (w' i ^ 2 / w' j + (-w' i) ^ 2 / w' i) =
      w' i * (v * (1 / w' j + 1 / w' i)) := by
    field_simp
  rw [e1, e2] at h_fo
  have key : -(ε / v) - v * (1 / w' j + 1 / w' i) ≤
      (η * ℓ j + log (w' j) - log (w j)) - (η * ℓ i + log (w' i) - log (w i)) := by
    have : w' i * (-(ε / v) - v * (1 / w' j + 1 / w' i)) ≤
        w' i * ((η * ℓ j + log (w' j) - log (w j)) - (η * ℓ i + log (w' i) - log (w i))) := by
      linarith
    exact le_of_mul_le_mul_left this hwi
  linarith

variable {T : ℕ} {ℓ : ℕ → α → ℝ} {a : ℕ → α → ℝ}

/-- **The balance of an approximate trajectory** [SSKM26, Lemma 33], corrected, for the negative
entropy. Let `a` be a trajectory with positive coordinates up to round `T ≥ 1` whose terms
`a (t + 1)` are `ε`-approximate steps from `a t` for the losses `ℓ t`, with
`ε ≤ ψ / (8 T²)` and `ψ > 0`. If `s ≤ t ≤ T` and the weights of the arms `i` and `j` are at least
`ψ` at the rounds `s < r ≤ t`, then the balance between `s` and `t` is at most
`η (L_{[s,t)}(j) - L_{[s,t)}(i)) + 1`. -/
lemma log_sub_log_add_le_sum_add_one (hpos : ∀ t ≤ T, ∀ k, 0 < a t k)
    (ha : ∀ t < T, IsApproxMirrorDescentStep (simplex α) negEntropy η
      (∑ i, ℓ t i • ContinuousLinearMap.proj i) (a t)
      (∑ i, log (a t i) • ContinuousLinearMap.proj i) ε (a (t + 1)))
    (hT : 1 ≤ T) {ψ : ℝ} (hψ : 0 < ψ) (hε : ε ≤ ψ / (8 * T ^ 2)) {s t : ℕ} (hst : s ≤ t)
    (htT : t ≤ T) {i j : α} (hψa : ∀ r, s < r → r ≤ t → ψ ≤ a r i ∧ ψ ≤ a r j) :
    log (a s j) - log (a t j) + (log (a t i) - log (a s i)) ≤
      η * ∑ r ∈ Ico s t, (ℓ r j - ℓ r i) + 1 := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  -- the stronger bound with `(t - s) / T` in place of `1`, by induction on `t`
  suffices key : ∀ t, s ≤ t → t ≤ T → (∀ r, s < r → r ≤ t → ψ ≤ a r i ∧ ψ ≤ a r j) →
      log (a s j) - log (a t j) + (log (a t i) - log (a s i)) ≤
        η * ∑ r ∈ Ico s t, (ℓ r j - ℓ r i) + ((t : ℝ) - s) / T by
    refine (key t hst htT hψa).trans (add_le_add_right ?_ _)
    rw [div_le_one hT0]
    have : (t : ℝ) ≤ T := by exact_mod_cast htT
    linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
  intro t hst
  induction t, hst using Nat.le_induction with
  | base => simp
  | succ t hst ih =>
    intro htT hψa'
    have htT' : t < T := htT
    have ih' := ih htT'.le fun r hr hrt ↦ hψa' r hr (hrt.trans t.le_succ)
    rw [sum_Ico_succ_top hst, Nat.cast_succ]
    -- the round `t`
    have h_round : log (a t j) - log (a (t + 1) j) + (log (a (t + 1) i) - log (a t i)) ≤
        η * (ℓ t j - ℓ t i) + 1 / T := by
      rcases eq_or_ne i j with rfl | hij
      · have h0 : log (a t i) - log (a (t + 1) i) + (log (a (t + 1) i) - log (a t i)) = 0 := by
          ring
        rw [h0, sub_self, mul_zero, zero_add]
        positivity
      have hψt := hψa' (t + 1) (Nat.lt_succ_of_le hst) le_rfl
      set v := ψ / (4 * T) with hv_def
      have hv : 0 < v := by positivity
      have hvψ : v ≤ ψ := by
        rw [hv_def, div_le_iff₀ (by positivity)]
        nlinarith
      have h1 := log_sub_log_add_le_of_isApproxMirrorDescentStep_negEntropy
        (hpos t htT'.le) (hpos (t + 1) htT) (ha t htT') hij hv (hvψ.trans hψt.1)
      have h2 : ε / v ≤ 1 / (2 * T) := by
        rw [div_le_iff₀ hv]
        calc ε ≤ ψ / (8 * T ^ 2) := hε
          _ = 1 / (2 * T) * v := by
            rw [hv_def]
            field_simp
            ring
      have h3 : v * (1 / a (t + 1) j + 1 / a (t + 1) i) ≤ 1 / (2 * T) := by
        have hj : 1 / a (t + 1) j ≤ 1 / ψ := one_div_le_one_div_of_le hψ hψt.2
        have hi : 1 / a (t + 1) i ≤ 1 / ψ := one_div_le_one_div_of_le hψ hψt.1
        calc v * (1 / a (t + 1) j + 1 / a (t + 1) i) ≤ v * (1 / ψ + 1 / ψ) :=
              mul_le_mul_of_nonneg_left (add_le_add hj hi) hv.le
          _ = 1 / (2 * T) := by
            rw [hv_def]
            field_simp
            ring
      have : 1 / (2 * (T : ℝ)) + 1 / (2 * T) = 1 / T := by
        field_simp
        ring
      linarith
    have e : ((t : ℝ) + 1 - s) / T = (t - s) / T + 1 / T := by ring
    rw [e]
    linarith

end Schlisselberg2026Hidden
