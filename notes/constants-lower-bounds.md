# Lower bounds by stuck trajectories: corrected statements and explicit constants

Area C of the constants review of [SSKM26] (arXiv:2511.22283v2): Lemma 14 (`lem:balance lower
bound` and its appendix restatement), Theorem 4 (`thm:lb_barrier_adversarial`), Theorem 35
(`thm:dimension lower bound`) and Theorem 36 (the unlabelled theorem after Theorem 35), with the
tools Lemma 24 (`lem:max step`) and Lemma 34 (`lem:stuck`). Conventions: `notes/modelling.md`.

Every statement below is meant to be true for all parameters in its stated range. Each was
checked numerically (Section 4) on the grid `η ∈ [1e-4, 1]` (and `η` up to `100` to locate the
failures outside the range), `T ∈ [1, 10⁶]`, `d ∈ {2, 3, 10, 1000}`, with high precision.

Summary of the changes:

| Result | Paper | Corrected |
| --- | --- | --- |
| Lemma 14 | `d = 2`, `α ≤ T/2`, `ε ≥ 4ηe^{-ηα}`, regret `Ω(T - 2α)` | every `d ≥ 2`, `0 < η ≤ 1`, `0 ≤ α ≤ T/2`, `ε ≥ 4ηe^{-ηα}`, uniform start, regret `≥ (T - 2α)/2` |
| Theorem 4 | `d ≥ 2`, `ε ≥ 4ηe^{-ηT/3}`, regret `Ω(T)` | same with `0 < η ≤ 1`, uniform start, regret `≥ T/6` for every `T` (optional: every `η > 0`, regret `≥ T/10`) |
| Theorem 35 | `ε ≥ 4η²/(c₁d^ν)`, regret `Ω(T)` | same with `0 < η ≤ c₁d^{ν-1}/(3ν)`, uniform start, regret `= T(1 - 1/d) ≥ T/2`; comparisons with positive points (Lean boundary issue, §1.5) |
| Theorem 36 | `k ≤ Tη/20`, `ε = 4ηe^{-k/2}`, regret `Ω(T)` | `τ ∈ ℕ` (`k = 2ητ`), `T ≥ 40τ`, `0 < η ≤ 1`, every `ε ≥ 4ηe^{-ητ}`, regret `≥ T/3`, plus the two properties the theorem is about |
| Lemma 34 (tool) | `d = 2`, `(4η/c₁)(w^i)^ν ≤ ε` | false as stated; corrected: `η ≤ c₁(w^i)^{1-ν}/(3ν)`, `ε ≥ 2η²(w^i)^ν/c₁`, any `d ≥ 2` with losses constant off `i`; for the negative entropy a closed form |
| Lemma 24 (tool) | `< 4η/h + √(ε/h)`, `h` = min of `r''` at the endpoints | `≤ 4η/h + √(2ε/h)`, `h` a lower bound of `r''` on the segment |

The headline proofs for the negative entropy (Lemma 14, Theorems 4, 36) no longer use Lemma 24 or
Lemma 34: they use the Gibbs variational principle (in LMLExplore) and an explicit formula for the
error of staying put. Theorem 35 uses a one-dimensional replacement of Lemma 24 (Lemma 35.A).

## 0. Notation

- `ι` is the finite index type (called `α` in `notes/modelling.md`; here `α` is the balance
  parameter of the paper), `d = Fintype.card ι ≥ 2`, `Δ = simplex ι`, `u₀ = fun _ ↦ 1/d`.
- `e_i = Pi.single i 1`, `𝟙 = fun _ ↦ 1`, `⟨ℓ, w⟩ = ∑ i, ℓ i * w i`, `L^i_{[s,t)} = ∑_{s ≤ r < t} ℓ_r^i`.
- Negative entropy: `F = negEntropy`, gradient at `w` the functional `h ↦ ∑ i, log (w i) * h i`
  (as in `LMLExplore.bregDiv_negEntropy`). For `w ∈ Δ` positive and `b ∈ Δ`,
  `D(b, w) := bregDiv F b w (∇F w) = ∑ i, b i * log (b i / w i)` (`bregDiv_negEntropy`).
- Step objective: `φ_{w,ℓ}(b) = η⟨ℓ, b⟩ + D(b, w)`. "`x` is an ε-step from `w` for `ℓ`" means
  `IsApproxMirrorDescentStep Δ F η ⟨ℓ, ·⟩ w (∇F w) ε x`: `x ∈ Δ` and
  `φ_{w,ℓ}(x) ≤ φ_{w,ℓ}(b) + ε` for all `b ∈ Δ`.
- Multiplicative weights: `Z_η(w, ℓ) = ∑ j, w j * exp (-η ℓ j)`,
  `MW(w, ℓ) = fun i ↦ w i * exp (-η ℓ i) / Z_η(w, ℓ)` (LMLExplore's `softmax` of
  `log w - η ℓ`).
- `ψ(x) = e^x - 1 - x ≥ 0`, and for `m ∈ [0, 1]`, `G_η(m) = log(1 + m(e^η - 1)) - ηm`.
- A trajectory for `T` rounds is `a : ℕ → ι → ℝ` with `a 0 = u₀` (always the uniform point
  here), positive (`∀ t i, 0 < a t i`), and `a (t+1)` an ε-step from `a t` for `ℓ t`, `∀ t < T`.
  Regret: `regret ℓ a u T = ∑ t < T, (⟨ℓ t, a t⟩ - ⟨ℓ t, u⟩)`.
- `τ = ⌊α⌋₊` (`Nat.floor`). All constants `e` below are `Real.exp 1`; we use only
  `7/3 < e < 3` (`Real.exp_one_gt_d9`, `Real.exp_one_lt_d9`).

## 1. Corrected statements

### 1.1 Lemma 14 (`lem:balance lower bound`; Lean `exists_approxMirrorDescent_le_regret_of_balanced`)

**Hypotheses.** `ι` finite with `d = card ι ≥ 2`, a coordinate `i₁ : ι`, `0 < η ≤ 1`, `T : ℕ`,
`α : ℝ` with `0 ≤ α` and `2α ≤ T`.

**Construction** (chosen before `ε`; the losses depend on `T, α, i₁` only, not on `η` or `ε`; the
trajectory depends on `η` but not on `ε`). With `τ = ⌊α⌋₊`:
- `ℓ t = e_{i₁}` for `t < τ`, `ℓ t = 𝟙 - e_{i₁}` for `t ≥ τ`;
- `a t` = `min(t, τ)` exact steps from `u₀` with the loss `e_{i₁}`: explicitly `a t i₁ = p_{min(t,τ)}` and `a t j = (1 - p_{min(t,τ)})/(d-1)`
  for `j ≠ i₁`, where `p_k = 1/(1 + (d-1)e^{ηk})`. So `a 0 = u₀`, `a (t+1) = MW(a t, ℓ t)` for
  `t < τ`, and `a (t+1) = a t` for `t ≥ τ`.

**Conclusion** (the headline is `∃ ℓ a, (1) ∧ … ∧ (5)`; the paper's `∃ ℓ, ∀ ε, ∃ a` is weaker):
1. `∀ t i, ℓ t i ∈ [0, 1]`;
2. `i₁` minimizes the cumulative loss, `∀ i, L^{i₁}_{[0,T)} ≤ L^i_{[0,T)}`, and the losses are
   α-balanced (modelling's notion): `∀ s ≤ t ≤ T, ∀ i, L^{i₁}_{[s,t)} - L^i_{[s,t)} ≤ α`;
3. `a 0 = u₀`, `∀ t, a t ∈ Δ`, `∀ t i, 0 < a t i`;
4. `∀ ε, 4ηe^{-ηα} ≤ ε → ∀ t < T`, `a (t+1)` is an ε-step from `a t` for `ℓ t`;
5. `regret ℓ a e_{i₁} T ≥ (T - 2α)/2` (the proof gives `(1 - 1/d)(T - 2α)`).

Since `e_{i₁}` minimizes `∑_{t<T} ⟨ℓ t, ·⟩` over `Δ` (by 2), (5) is the paper's `Regret(w*)`.

### 1.2 Theorem 4 (`thm:lb_barrier_adversarial`; Lean `exists_approxMirrorDescent_le_regret_negEntropy`)

**Hypotheses.** `ι` finite with `d = card ι ≥ 2`, `0 < η ≤ 1`, `T : ℕ` (any, including
`T = 0, 1, 2`), `ε` with `4ηe^{-ηT/3} ≤ ε`.

**Conclusion.** There exist losses `ℓ` with `∀ t i, ℓ t i ∈ [0,1]` and a trajectory `a` with
`a 0 = u₀`, positive, `a (t+1)` an ε-step from `a t` for `ℓ t` for all `t < T`, and a point
`u ∈ Δ` with `∀ v ∈ Δ, ∑_{t<T} ⟨ℓ t, u⟩ ≤ ∑_{t<T} ⟨ℓ t, v⟩` and `regret ℓ a u T ≥ T/6`.

Stronger form (free from the proof): `ℓ` depends on `T` only, `a` on `η, T`, and `a` works for
every `ε ≥ 4ηe^{-ηT/3}` simultaneously. It is Lemma 14 with `α = T/3`.

**Optional extension, every `η > 0`.** For `η ≥ 1`, the exact trajectory (ε = 0) of the
alternating losses `ℓ t = 𝟙 - e_{i₂}` (`t` even), `𝟙 - e_{i₁}` (`t` odd), `i₁ ≠ i₂`, has regret
`≥ T/10` against `e_{i₂}`. Together: for every `η > 0` and `ε ≥ 4ηe^{-ηT/3}` (indeed every
`ε ≥ 0` when `η ≥ 1`) there is a trajectory with regret `≥ T/10`. Whether to state this is a
choice: for `η ≥ 1` exact mirror descent already has linear regret, so the extension says nothing
about approximation; I recommend the `η ≤ 1` statement as the headline.

### 1.3 Theorem 35 (`thm:dimension lower bound`; Lean `exists_approxMirrorDescent_le_regret_of_isPowerBarrier`)

**Hypotheses.** `ι` finite with `d = card ι ≥ 2`, `i₀ : ι`; `r : ℝ → ℝ` with
`IsPowerBarrier ν c₁ c₂ r` (only `1 ≤ ν`, `0 < c₁`, twice differentiable on `(0,1)` and
`c₁/x^ν ≤ r'' x` are used); `R w = ∑ i, r (w i)` with gradient `h ↦ ∑ i, deriv r (w i) * h i`;
`0 < η ≤ c₁ d^{ν-1}/(3ν)`; `ε ≥ 4η²/(c₁ d^ν)`; `T : ℕ`. Decision set: see §1.5 (recommended:
`K° = {w ∈ Δ : ∀ i, 0 < w i}`; alternative: `K = Δ` with `ContinuousOn r (Set.Icc 0 1)`).

**Conclusion.** With the constant losses `ℓ t = 𝟙 - e_{i₀}` (in `[0,1]^ι`) and the constant
trajectory `a t = u₀`: `a (t+1)` is an ε-step from `a t` for `ℓ t` for every `t` (so for every
`T`), `a` is positive, `e_{i₀}` minimizes the cumulative loss over `Δ`, and
`regret ℓ a e_{i₀} T = T(1 - 1/d) ≥ T/2`.

The paper's threshold `4η²/(c₁d^ν)` is kept; the proof gives `(e/2)η²/(c₁d^ν)`. Negative entropy:
`ν = c₁ = 1`, so `η ≤ 1/3` and `ε ≥ 4η²/d`.

### 1.4 Theorem 36 (unlabelled, after Theorem 35; Lean `exists_approxMirrorDescent_le_regret_negEntropy_threePhase`)

**Hypotheses.** `ι` finite with `card ι = 2`, `i₁ ≠ i₂` its two elements (so `𝟙 - e_{i₁} = e_{i₂}`),
`0 < η ≤ 1`, `τ : ℕ`, `T : ℕ` with `40τ ≤ T` (the paper's `k = 2ητ`; `k ≤ Tη/20` is `40τ ≤ T`).

**Construction** (independent of `ε`): losses `ℓ t = e_{i₂}` (paper's `(0,1)`) for
`t < 3τ`, `ℓ t = e_{i₁}` (paper's `(1,0)`) for `3τ ≤ t < 5τ`, `ℓ t = e_{i₂}` for `t ≥ 5τ`.
Trajectory: `a t i₁ = 1/(1 + e^{η E_t})` (and `a t i₂ = 1 - a t i₁`) with the "effective
cumulative difference" `E_t = -min(t, τ)` for `t ≤ 3τ`, `E_t = t - 4τ` for `3τ ≤ t ≤ 5τ`,
`E_t = τ` for `t ≥ 5τ`: exact steps for `t < τ` and `3τ ≤ t < 5τ`, `a (t+1) = a t` otherwise.

**Conclusion.**
1. `∀ t i, ℓ t i ∈ [0, 1]`; `i₁` minimizes the cumulative loss (`L^{i₁} = 2τ ≤ T - 2τ = L^{i₂}`);
   the losses are `2τ`-balanced;
2. the exact trajectory stays away from 0 on the optimal arm: every 0-approximate trajectory `b`
   from `u₀` (the exact one is unique) has `b t i₁ ≥ 1/2` for all `t ≤ T` (the property that
   distinguishes this theorem from Lemma 14);
3. `a 0 = u₀`, `a` positive, and `∀ ε ≥ 4ηe^{-ητ}`, `∀ t < T`, `a (t+1)` is an ε-step from `a t`;
4. `regret ℓ a e_{i₁} T ≥ T/3` (the proof gives `(T - 9τ)/2 ≥ 31T/80`; numerically `≥ 0.45T`).

In terms of the balance `α = 2τ`, the threshold is `4ηe^{-ηα/2}`. If (2) is too costly, the
explicit-trajectory form "`b t = MW^t(u₀)` has `b t i₁ ≥ 1/2`" avoids the uniqueness of exact
steps.

### 1.5 The boundary issue for general barriers (Lean modelling, needs a decision)

`IsApproxMirrorDescentStep K F η y a F' ε x` compares `x` with every `b ∈ K`. On the closed
simplex, `b` may have zero coordinates, where `R b = ∑ r (b i)` uses `r 0`, which a power barrier
does not constrain (and for `ν ≥ 2` the true value is `+∞`). In Lean, `r = fun x ↦ -Real.log x`
has `r 0 = 0`, so `bregDiv R e_j u₀ = -d log d < 0` and `φ(e_j) ≤ η - d log d`, while
`φ(x) ≥ 0` for positive `x`: no positive point is an ε-step from `u₀` when
`η + ε < d log d` (`boundary_junk.py`). Consequences: existence statements for general barriers
(Theorem 35, Lemma 34) are false in Lean as modelled, and the upper bound Theorem 6 is vacuous for
the log barrier. Options:
- (recommended) state barrier results on `K° = {w ∈ Δ : ∀ i, 0 < w i}`. The positivity
  hypothesis on iterates becomes membership in `K°`, the comparison points are positive, and
  `u₀ ∈ K°`. The regret comparator `u` can still be any point of `Δ` (`regret` takes any `u`);
- keep `K = Δ` and assume `ContinuousOn r (Set.Icc 0 1)`: then Lemma 35.C extends the
  comparisons to the boundary, but the hypothesis is unsatisfiable for `ν ≥ 2` (a `ν`-barrier
  with `ν ≥ 2` is unbounded at `0`), so the log barrier is lost.

For the negative entropy (Lemma 14, Theorems 4, 36) there is no issue: `negEntropy` is
continuous on `[0,1]` in Lean, and the Gibbs inequality of LMLExplore holds on all of `Δ`.

## 2. Blueprint

Lemmas are named after the paper's results they replace or prove. "MVT" is the mean value
theorem (`exists_deriv_eq_slope` / `exists_hasDerivAt_eq_slope`).

### 2.1 Negative entropy tools (replace Lemmas 24 and 34 for `ν = 1`)

**Lemma G (Gibbs; in LMLExplore).** Let `w ∈ Δ` with `∀ i, 0 < w i`, `ℓ : ι → ℝ`, `η ∈ ℝ`. For every
`b ∈ Δ`, `φ_{w,ℓ}(b) ≥ -log Z_η(w, ℓ)`, with equality at `b = MW(w, ℓ)`.
*Proof.* `bregDiv_negEntropy` gives `φ(b) = η⟨ℓ,b⟩ + ∑ b_i log(b_i/w_i)` (its hypothesis
`w i = 0 → b i = 0` is vacuous). LMLExplore `sum_mul_sub_sum_mul_log_div_le_log_sum_mul_exp`
with `p = w`, `q = b`, `v = -ηℓ` reads `-η⟨ℓ,b⟩ - ∑ b_i log(b_i/w_i) ≤ log Z`. For
`b = m := MW(w,ℓ)` (positive, in `Δ`): `log(m_i/w_i) = -ηℓ_i - log Z`, so
`∑ m_i log(m_i/w_i) = -η⟨ℓ,m⟩ - log Z` and `φ(m) = -log Z`. (`isGreatest_sum_mul_sub_sum_mul_log_div`
packages both facts.) ∎

**Lemma 34.NE-a (exact step).** `MW(w, ℓ)` is an ε-step from `w` for `ℓ`, for every `ε ≥ 0`, and
is positive. *Proof.* Lemma G: `φ(MW) = -log Z ≤ φ(b) ≤ φ(b) + ε`. Positivity: quotient of
positive numbers. ∎

**Lemma 34.NE-b (staying put).** For `w ∈ Δ` positive, `w` is an ε-step from `w` for `ℓ` as soon
as `η⟨ℓ, w⟩ + log Z_η(w, ℓ) ≤ ε`. *Proof.* `φ(w) = η⟨ℓ,w⟩` since `bregDiv F w w _ = 0`, and
`φ(b) + ε ≥ -log Z + ε ≥ η⟨ℓ,w⟩` by Lemma G. ∎ (The converse also holds, by `b = MW`.)

**Lemma 34.NE-c (closed form).** For `ℓ = 𝟙 - e_{i₀}` and `m = w i₀`:
`η⟨ℓ,w⟩ + log Z = G_η(m) = log(1 + m(e^η - 1)) - ηm`.
*Proof.* `⟨ℓ,w⟩ = 1 - m`, `Z = m + (1-m)e^{-η}`, and
`η(1-m) + log(m + (1-m)e^{-η}) = log(e^{-ηm}(me^η + 1 - m)) = log(1 + m(e^η - 1)) - ηm`. ∎

**Lemma 34.NE-d (bounds on `G`).** For `η ≥ 0`, `m ∈ [0,1]`:
1. `G_η(m) ≤ m ψ(η) = m(e^η - 1 - η)`;
2. `G_η(m) ≤ (1-m) ψ(-η) = (1-m)(e^{-η} - 1 + η)`;
3. if `η ≤ 1`: `G_η(m) ≤ η² m` and `G_η(m) ≤ η²(1-m)`.

*Proof.* (1) `log y ≤ y - 1` (`Real.log_le_sub_one_of_pos`) at `y = 1 + m(e^η-1) > 0`.
(2) `1 + m(e^η - 1) = e^η (1 - (1-m)(1-e^{-η}))`, so `G = η(1-m) + log(1 - (1-m)(1-e^{-η}))`; the
argument is in `(0,1]` because `(1-m)(1-e^{-η}) < 1`; apply `log y ≤ y - 1`.
(3) `Real.abs_exp_sub_one_sub_id_le : |x| ≤ 1 → |exp x - 1 - x| ≤ x²` at `x = η` and `x = -η`. ∎

**Lemma 34.NE (stuck, negative entropy).** If `w ∈ Δ` is positive, `ℓ = 𝟙 - e_{i₀}`, `0 < η ≤ 1`,
`m = w i₀`, and `ε ≥ η²m` or `ε ≥ η²(1-m)`, then `w` is an ε-step from `w` for `ℓ`.
*Proof.* 34.NE-b, -c, -d(3). ∎

**Lemma MW-iter (iterated steps).** For `w` positive and losses `ℓ_0, …, ℓ_{k-1}`, iterating MW
gives `fun i ↦ w i * exp(-η ∑_{s<k} ℓ_s i) / Z`. In particular, from `u₀` with `k` losses `e_{i₁}`:
`i₁ ↦ p_k := 1/(1 + (d-1)e^{ηk})`, `j ↦ (1-p_k)/(d-1) = e^{ηk}/(1+(d-1)e^{ηk})` (`j ≠ i₁`).
*Proof.* Induction; `MW(MW(w,ℓ),ℓ') = MW(w, ℓ + ℓ')` (the normalizations cancel). ∎

**Lemma P (facts on `p_k`).** `p_0 = 1/d ≤ 1/2`; `k ↦ p_k` is antitone; `p_k ≤ e^{-ηk}/(d-1) ≤ e^{-ηk}`.

### 2.2 Lemma 14 and Theorem 4

**Lemma 14.A (losses).** With `ℓ` as in §1.1: `ℓ t i ∈ {0,1}`. If `τ ≤ T`:
`L^{i₁}_{[0,T)} = τ` and `L^j_{[0,T)} = T - τ` for `j ≠ i₁`; so `2τ ≤ T` gives the minimality of
`i₁`. For `s ≤ t` and `j ≠ i₁`: `L^{i₁}_{[s,t)} - L^j_{[s,t)} = #([s,t) ∩ [0,τ)) - #([s,t) \ [0,τ))
≤ #([s,t) ∩ [0,τ)) ≤ τ`; for `j = i₁` the difference is `0 ≤ α`.
Since `τ = ⌊α⌋₊ ≤ α` (`Nat.floor_le`, `α ≥ 0`), the losses are α-balanced, and `2τ ≤ 2α ≤ T`. ∎

**Lemma 14.B (the trajectory is valid).** `a t ∈ Δ` and positive for all `t`. For `t < τ`, `a (t+1)
= MW(a t, e_{i₁})` (MW-iter), an ε-step for every `ε ≥ 0` (34.NE-a). For `t ≥ τ`, `a (t+1) =
a t = a τ`, and `a τ i₁ = p_τ`, so by Lemma 34.NE (first alternative) `a (t+1)` is an ε-step
whenever `ε ≥ η²p_τ`. ∎

**Lemma 14.C (threshold).** If `0 < η ≤ 1` and `α ≥ 0` then `η² p_τ ≤ 4η e^{-ηα}`.
*Proof.* `p_τ ≤ e^{-ητ}` (P); `α < τ + 1` (`Nat.lt_floor_add_one`) gives
`e^{-ητ} ≤ e^{η} e^{-ηα} ≤ e · e^{-ηα}` (`η ≤ 1`); and `e η² ≤ 3η ≤ 4η` (`η ≤ 1`, `e < 3`). ∎
(So the trajectory is in fact `(e/(d-1)) η² e^{-ηα}`-approximate.)

**Lemma 14.D (regret).** If `2τ ≤ T`:
`regret ℓ a e_{i₁} T = ∑_{t<τ} (p_t - 1) + (T - τ)(1 - p_τ) ≥ (1 - p_τ)(T - 2τ) ≥ (1 - 1/d)(T - 2τ)`.
*Proof.* `⟨e_{i₁}, a t⟩ = p_t`, `⟨e_{i₁}, e_{i₁}⟩ = 1` (`t < τ`); `⟨𝟙 - e_{i₁}, a t⟩ = 1 - p_τ`,
`⟨𝟙 - e_{i₁}, e_{i₁}⟩ = 0` (`t ≥ τ`). For `t < τ`, `p_t ≥ p_τ` (P), so `p_t - 1 ≥ -(1 - p_τ)`; sum.
Last step: `p_τ ≤ p_0 = 1/d` and `T - 2τ ≥ 0`. ∎ (This is the step the paper's proof misses,
erratum LB8: the learner's losses in the first phase, `≥ p_τ` per round, offset the comparator's.)

**Proof of Lemma 14.** 14.A gives (1), (2); 14.B, 14.C give (3), (4); 14.D and
`T - 2τ ≥ T - 2α ≥ 0`, `1 - 1/d ≥ 1/2` give (5). ∎

**Proof of Theorem 4.** Lemma 14 with `α = T/3` (`0 ≤ T/3`, `2T/3 ≤ T`), `i₁` any coordinate,
`u = e_{i₁}`: the threshold is `4ηe^{-ηT/3}`, the regret is `≥ (T - 2T/3)/2 = T/6`, and the
minimality over `Δ` follows from that over the coordinates: for `v ∈ Δ`,
`∑_t ⟨ℓ t, v⟩ = ∑_i v_i L^i ≥ L^{i₁} ∑_i v_i = L^{i₁}`. ∎ No case split and no `T₀` are needed:
for `T ≤ 2`, `τ = 0` and the trajectory stays at `u₀` (gap `G_η(1/d) ≤ η²/d ≤ 4ηe^{-ηT/3}`).

**Theorem 4⁺ (optional, `η ≥ 1`).** Losses: `ℓ t = 𝟙 - e_{i₂}` for even `t`, `𝟙 - e_{i₁}` for odd
`t`; trajectory `a t = MW^t(u₀)` (exact). By MW-iter, at even `t = 2k` the cumulative losses are
`k, k, 2k` (for `i₁, i₂`, others), so `a t i₁ = a t i₂ ≤ 1/2` and the loss of round `t` is
`1 - a t i₂ ≥ 1/2`; at odd `t = 2k+1` they are `k+1, k, 2k+1`, so
`a t i₁ ≤ a t i₁/(a t i₁ + a t i₂) = 1/(1+e^η)` and the loss is `≥ 1 - 1/(1+e^η)`. With
`L^{i₂} = ⌊T/2⌋ ≤ L^{i₁} = ⌈T/2⌉ ≤ L^j = T`:
`regret ℓ a e_{i₂} T ≥ ⌈T/2⌉/2 - ⌊T/2⌋/(1+e^η) ≥ T/4 - (T/2)(3/10) = T/10`, using
`1/(1+e^η) ≤ 1/(1+e) ≤ 3/10` (`e ≥ 7/3`). ∎

### 2.3 Theorem 35 (general `ν`-barriers)

Here `r' = deriv r` and `r'' = deriv (deriv r)`; `r` and `r'` are differentiable on `(0,1)` by
`IsPowerBarrier`, so the MVT applies to both on every `[x, y] ⊂ (0,1)`. Standing facts, for `r` with `r'' ≥ c₁/x^ν > 0` on `(0,1)`: `r'` is strictly monotone on `(0,1)`
(MVT on `r'`), hence `D_r(y,x) := r y - r x - r' x (y - x) ≥ 0` for `x, y ∈ (0,1)` (MVT on `r`).
For `R w = ∑ i, r (w i)` with gradient `∑ i, r'(w i) h i`:
`bregDiv R b w _ = ∑ i, D_r(b i, w i)` (unfold `bregDiv`).

**Lemma 35.A (one-dimensional step bound; replaces Lemma 24).** Let `x ∈ (0,1)`, `ν ≥ 1`, `c₁ > 0`,
`r'' ≥ c₁/s^ν` on `(0,1)`, and `0 ≤ η ≤ c₁ x^{1-ν}/(3ν)`. Then for every `y ∈ (0,1)`:
`η|y - x| - D_r(y, x) ≤ (e/2) η² x^ν / c₁`.
*Proof.* Put `κ = c₁/(e x^ν)` and `z = x(1 + 1/ν)`.
- (A0) For `s ∈ (0, z]`: `s^ν ≤ z^ν = (1+1/ν)^ν x^ν ≤ e x^ν`, using `1 + 1/ν ≤ e^{1/ν}`
  (`Real.add_one_le_exp`) and monotonicity of `t ↦ t^ν`. Hence `r''(s) ≥ κ` on `(0, z] ∩ (0,1)`.
- (A1) For `y ∈ (0, z] ∩ (0, 1)`: `D_r(y,x) ≥ κ(y-x)²/2`. Proof:
  `g(y) = D_r(y,x) - κ(y-x)²/2` has `g(x) = 0` and `g'(y) = r'(y) - r'(x) - κ(y - x)`, which by
  MVT on `r'` and (A0) is `≥ 0` for `y ≥ x` and `≤ 0` for `y ≤ x`; so `g ≥ 0`.
- (A2) Hence for `y ∈ (0, z] ∩ (0, 1)`: `η|y-x| - D_r(y,x) ≤ η h - κh²/2 ≤ η²/(2κ) = (e/2)η²x^ν/c₁` with
  `h = |y - x|` (`η h ≤ η²/(2κ) + κ h²/2`).
- (A3) If `z < 1` and `y ∈ [z, 1)`: by MVT and (A0), `r'(z) - r'(x) ≥ κ(z - x) = c₁x^{1-ν}/(eν)
  ≥ c₁x^{1-ν}/(3ν) ≥ η` (`e ≤ 3`). By MVT on `r` and monotonicity of `r'`,
  `D_r(y,x) - D_r(z,x) = r y - r z - r'(x)(y - z) ≥ (r'(z) - r'(x))(y - z) ≥ η(y - z)`. So
  `η(y - x) - D_r(y,x) ≤ η(z - x) - D_r(z,x) ≤ (e/2)η²x^ν/c₁` by (A2) at `y = z`. ∎

The case `y < x` only needs `r'' ≥ c₁/x^ν` on `(y, x)` and gives `η²x^ν/(2c₁)`; the factor `e`
comes from `y > x`, where `r''` may be smaller than at `x` (this is what Lemmas 34 and 35 of the
paper get wrong, erratum LB4).

**Lemma 34′ (stuck, power barriers; corrected Lemma 34).** Let `w ∈ Δ` be positive, `i₀ : ι`,
`m = w i₀`, `ℓ : ι → ℝ` with `ℓ i₀ = a`, `ℓ j = c` for `j ≠ i₀`, `|c - a| ≤ 1` (e.g. any
`ℓ ∈ [0,1]^ι` constant off `i₀`; for `d = 2` every `ℓ ∈ [0,1]²`), `0 < η ≤ c₁ m^{1-ν}/(3ν)`,
`ε ≥ 2η² m^ν/c₁`. Then for every positive `b ∈ Δ`: `η⟨ℓ, w⟩ ≤ η⟨ℓ, b⟩ + bregDiv R b w _ + ε`;
i.e. `w` is an ε-step from `w` on `K°` (and on `Δ` under Lemma 35.C).
*Proof.* `∑(w - b) = 0` gives `⟨ℓ, w - b⟩ = (c - a)(b i₀ - m)`, so
`η⟨ℓ, w - b⟩ ≤ η|b i₀ - m|`. All `b j, w j ∈ (0,1)` (positivity and `d ≥ 2`), so
`bregDiv R b w _ ≥ D_r(b i₀, m)` (the other terms are `≥ 0`). By Lemma 35.A with `x = m`:
`η⟨ℓ, w - b⟩ - bregDiv R b w _ ≤ (e/2)η²m^ν/c₁ ≤ 2η²m^ν/c₁ ≤ ε`; and `bregDiv R w w _ = 0`. ∎

**Lemma 35.C (boundary, only for `K = Δ`).** If `ContinuousOn r (Set.Icc 0 1)`, `w, x` are fixed and
`φ(x) ≤ φ(b) + ε` for every positive `b ∈ Δ`, then it holds for every `b ∈ Δ`.
*Proof.* `b_s = (1-s)b + s u₀` is positive for `s ∈ (0,1]` and tends to `b`; `φ` is continuous on
`Δ` (the gradient term is linear); pass to the limit. ∎

**Proof of Theorem 35.** Lemma 34′ at `w = u₀`, `m = 1/d`, `ℓ = 𝟙 - e_{i₀}` (`a = 0, c = 1`): its
hypotheses are `η ≤ c₁ d^{ν-1}/(3ν)` and `ε ≥ 2η²/(c₁d^ν)`, implied by `ε ≥ 4η²/(c₁d^ν)`. Every step
is this same step. Regret: `∑_{t<T} (⟨𝟙 - e_{i₀}, u₀⟩ - ⟨𝟙 - e_{i₀}, e_{i₀}⟩) = T(1 - 1/d) ≥ T/2`;
`e_{i₀}` minimizes as in Theorem 4 (`L^{i₀} = 0`). ∎

### 2.4 Theorem 36

**Lemma 36.A (losses).** With `ℓ` as in §1.4 and `T ≥ 5τ`: `L^{i₁}_{[0,T)} = 2τ`,
`L^{i₂}_{[0,T)} = T - 2τ`, so `i₁` minimizes when `T ≥ 4τ`. For `s ≤ t`:
`L^{i₁}_{[s,t)} - L^{i₂}_{[s,t)} = #([s,t) ∩ [3τ,5τ)) - #([s,t) \ [3τ,5τ)) ≤ 2τ`. ∎

**Lemma 36.B (exact trajectory).** With `D_t = L^{i₁}_{[0,t)} - L^{i₂}_{[0,t)}`: `D_t = -t` (`t ≤ 3τ`),
`D_t = t - 6τ ≤ -τ` (`3τ ≤ t ≤ 5τ`), `D_t = 4τ - t ≤ -τ` (`t ≥ 5τ`); so `D_t ≤ 0` for all `t`. A
0-approximate step from a positive `w` is `MW(w, ℓ)` (uniqueness: `φ(x) = φ(MW)` forces
`KL(x‖MW) = 0`, `x = MW` by the equality case of `log y ≤ y - 1`; or use the explicit form), so by
MW-iter the exact trajectory is `b t i₁ = 1/(1 + e^{ηD_t}) ≥ 1/2`. ∎

**Lemma 36.C (the trajectory is valid).** By MW-iter, `a` as defined satisfies
`a (t+1) = MW(a t, ℓ t)` for `t < τ` and `3τ ≤ t < 5τ` (these steps change `E` by `-1`, resp.
`+1`), and `a (t+1) = a t` otherwise. In particular `a τ i₁ = 1/(1+e^{-ητ})`, `a (4τ) = u₀`,
`a (5τ) i₁ = q := 1/(1+e^{ητ})`. Steps:
- exact steps: ε-steps for every `ε ≥ 0` (34.NE-a);
- `τ ≤ t < 3τ`: loss `e_{i₂} = 𝟙 - e_{i₁}`, `m = a τ i₁`, `1 - m = q ≤ e^{-ητ}`: Lemma 34.NE
  (second alternative) needs `ε ≥ η² q`;
- `t ≥ 5τ`: loss `𝟙 - e_{i₁}`, `m = q`: Lemma 34.NE (first alternative) needs `ε ≥ η² q`.
Since `η²q ≤ η² e^{-ητ} ≤ 4ηe^{-ητ}` (`η ≤ 1`), all steps are ε-steps for `ε ≥ 4ηe^{-ητ}`. ∎

**Lemma 36.D (regret).** If `T ≥ 5τ`: `regret ℓ a e_{i₁} T ≥ (T - 5τ)(1 - q) - 2τ ≥ (T - 9τ)/2`.
*Proof.* The learner's losses are `≥ 0` for `t < 5τ`, and `⟨e_{i₂}, a t⟩ = 1 - q ≥ 1/2` for `t ≥ 5τ`
(`q ≤ 1/2`); the comparator `e_{i₁}` pays `L^{i₁} = 2τ`. ∎ (Accounting for the phase `[3τ, 5τ)`,
where the learner pays `τ + 1/2 - q ≥ τ`, gives `(T - 7τ)/2`.)

**Proof of Theorem 36.** 36.A (1), 36.B (2), 36.C (3), and 36.D with `T ≥ 40τ`:
`(T - 9τ)/2 ≥ (T - 9T/40)/2 = 31T/80 ≥ T/3`. ∎

### 2.5 Reference: corrected Lemma 24 (used by other areas, not by these proofs)

**Lemma 24 (corrected).** Let `R w = ∑ i, r (w i)` with `r` differentiable, `w, x ∈ Δ`, `x` an
ε-step from `w` for a loss `ℓ` with `∀ j, |ℓ j| ≤ 1`, `i : ι`, and `h > 0` with `r''(s) ≥ h` for every
`s` in the closed segment between `w i` and `x i` (for a power barrier with both points in `(0,1)`:
`h = c₁/max(w i, x i)^ν`). Then `|x i - w i| ≤ 4η/h + √(2ε/h)`. With `ℓ ∈ [0,1]^ι`,
`4η/h` improves to `2η/h`. *Proof.* The paper's, with `D_r(x i, w i) ≥ (h/2)(x i - w i)²` from the
lower bound on the whole segment, and Lemma 21 with `a = h/2`, `b = 2η`, `c = ε`
(`b/a = 4η/h`, `c/a = 2ε/h`); use `≤` (Lemma 21 needs `c > 0` for `<`). The hypothesis `η ≤ 1/4`
is not used. ∎

## 3. Errata (area C)

Numbered `LB1, …` for this note; to be merged into `notes/paper-errata.md` as `E…` entries.

| # | Location (v2) | Error | Correction | Kind |
| --- | --- | --- | --- | --- |
| LB1 | Lemma 24 (`lem:max step`), statement and last display | `√(ε/h)`: Lemma 21 with `a = h/2, b = 2η, c = ε` gives `√(2ε/h)`. Counterexample: negative entropy, `d = 1000`, `w = u₀`, `ℓ = 0`, `η = 1e-8`, `ε = 1e-6`: an ε-step with `\|Δ\| = 4.503e-5 >` the paper's bound `3.233e-5` (corrected bound `4.572e-5`) | `\|w_t^i - w_{t+1}^i\| ≤ 4η/h + √(2ε/h)` (`≤`, not `<`, for `ε = 0`) | wrong constant |
| LB2 | Lemma 24, definition of `h` and "From Taylor inequality" | `h = min{r''(w_t^i), r''(w_{t+1}^i)}`, but the Taylor bound needs `r'' ≥ h` on the whole segment; endpoint values suffice only for monotone `r''` (Definition 18, not Definition 1). Also uses `‖ℓ_t‖_∞ ≤ 1` implicitly; `η ≤ 1/4` unused | `h` a lower bound of `r''` on the segment, e.g. `c₁/max(w_t^i, w_{t+1}^i)^ν`; assume `\|ℓ_t^j\| ≤ 1` | gap in the proof |
| LB3 | Lemma 25 (`lem:not_too_far`), eq. (single_step_relation) — other area | Inherits LB1, LB2. The display has `4c₁ηw` and `√(c₁εw)` where Lemma 24 (with `h ≥ c₁/(w_t^i)^ν` on the segment) gives `4η(w_t^i)^ν/c₁` and, corrected, `√(2ε(w_t^i)^ν/c₁)`. For `ν = c₁ = 1` the hypotheses `η ≤ 1/16`, `ε ≤ w_t^i/16` then give only `w_{t±1}^i ≥ (3/4 - 1/(2√2)) w_t^i ≈ 0.40 w_t^i`, not `w_t^i/2`; for `c₁ ≠ 1` the hypothesis `η ≤ 1/(16c₁)` should be `η ≤ c₁/16` | recheck the constants of Lemma 25 and of its users (upper-bound areas) | wrong constant (flag) |
| LB4 | Lemma 34 (`lem:stuck`), proof, and Theorem 35, proof | Lemma 24 is applied with `h = r''(w_t^i)` at the current point. Lemma 24's `h` also involves the other endpoint; the exact step moves the stuck coordinate up (Theorem 35: coordinate `d`), where `r''` is smaller | Lemma 35.A (bound `r''` on `[x, x(1+1/ν)]` by `c₁/(e x^ν)`) | gap in the proof |
| LB5 | Lemma 34, proof | From `\|w_t^i - w̃^i\| ≤ ε` it concludes `φ(w_t) ≤ φ(w̃) + ε`; the argument gives `φ(w_t) - φ(w̃) ≤ η⟨ℓ, w_t - w̃⟩ ≤ η\|w_t^i - w̃^i\| ≤ ηε` | needs `η ≤ 1` (or the hypothesis `4η²(w^i)^ν/c₁ ≤ ε`) | gap in the proof |
| LB6 | Lemma 34, statement | False as stated. (a) negative entropy (`ν = c₁ = 1`), `d = 2`, `η = 10`, `ε = 0.1`, `w = (ε/(4η), 1 - ε/(4η))`, loss `(0,1)`: the error of staying is `4.0015 > ε`. (b) `r = 0.01·x log x` (`c₁ = 0.01`), `η = 1`, `ε = 0.04`, `w^1 = c₁ε/(4η)`: `0.908 > ε`. (c) log barrier, `η = 100`, `w^1 = 0.03`, `ε = 4η(w^1)²`: error/ε `= 178` | Lemma 34′: `d ≥ 2`, losses in `[0,1]^d` constant off `i` (`d = 2`: all losses), `η ≤ c₁(w^i)^{1-ν}/(3ν)`, `ε ≥ 2η²(w^i)^ν/c₁` (implied by the paper's condition when also `η ≤ 2`); comparisons with positive points (§1.5). Negative entropy: Lemma 34.NE (`η ≤ 1`, `ε ≥ η² min(m, 1-m)`, loss `𝟙 - e_{i₀}`) | false statement |
| LB7 | Lemma 14, main text, and its proof (App. D) | The statement fixes the losses before `ε` ("there exists a sequence … such that for any ε"), but the proof's phase length `τ = (1/η)log(4η/ε)` depends on `ε`; `τ` is not an integer | `τ = ⌊α⌋₊`: losses depend on `(α, T)` only, the trajectory on `η` only; one trajectory works for every `ε ≥ 4ηe^{-ηα}` (Lemma 14.C, needs `η ≤ 1`) | gap in the proof |
| LB8 | Lemma 14, proof, last sentence | "regret for those steps is `Ω(T-τ)`. Adding the first `τ` steps we get `Ω(T - 2τ)`": with per-round regret `1 - w^1 ≥ 1/2` after `τ` and `≥ -1` before, this gives `(T-τ)/2 - τ = (T - 3τ)/2`, negative for `τ > T/3` although `T - 2τ > 0`; `w^1_τ ≤ ε/(4η)` is only `≤ 1/2` when `ε` is not `≪ η` | count the learner's first-phase losses `w_t^1 ≥ w_τ^1`: `Regret ≥ (1 - w_τ^1)(T - 2τ) ≥ (1 - 1/d)(T - 2τ)` (Lemma 14.D) | gap in the proof |
| LB9 | Lemma 14 (both versions) | No restriction on `η`, but the proof needs Lemma 34, false for large `η` (LB6). With the construction of Lemma 14.B (`τ = ⌊α⌋₊`, the error of staying is `≈ (e^η - 1 - η)e^{η(α-τ)}e^{-ηα}/(d-1)`) the error exceeds `4ηe^{-ηα}` from `η ≈ 1.3` (`α` just below an integer, `d = 2`) and from `η ≈ 2.65` (integer `α`, `d = 2`) | assume `0 < η ≤ 1`; the case `η > 1` is not claimed | missing hypothesis |
| LB10 | Lemma 14 (both versions), Theorem 4, Theorem 35 | The initial point of the trajectory is not specified (the lower bounds are trivial for a free start; the proofs use `w_1 = u₀`); `α ≥ 0` implicit | `a 0 = u₀`; `0 ≤ α` | missing hypothesis |
| LB11 | Lemma 14, main text | `Ω(T - 2α)`; stated for `d = 2` only | regret `≥ (T - 2α)/2` (indeed `(1 - 1/d)(T - 2α)`), for every `d ≥ 2` (generalization, needed by Theorem 4) | explicit constant |
| LB12 | Lemma 14, appendix restatement | "for some `α ≥ T/2`" (then `T - 2α ≤ 0`); loss range and `d = 2` dropped | `α ≤ T/2` | typo |
| LB13 | Proof of Theorem 4 (Sec. 5.3) | "Directly by applying Lemma 14 with `α = T/3`": Lemma 14 is for `d = 2`, Theorem 4 for `d ≥ 2`. (Padding the extra coordinates with loss `1` and using `𝟙 - e_{i₂}` in the first phase loses the compensation of LB8) | Lemma 14 for `d ≥ 2` with first-phase loss `e_{i₁}` (only the future best coordinate pays) | gap in the proof |
| LB14 | Theorem 4, statement | No restriction on `η`; the proof (via LB9) needs `η ≤ 1`. The statement itself holds for every `η > 0` with another construction (Theorem 4⁺: exact steps on alternating losses, regret `≥ T/10` for `η ≥ 1`) | assume `0 < η ≤ 1` (recommended), or add Theorem 4⁺ | missing hypothesis |
| LB15 | Theorem 4, statement | `Regret(w*) = Ω(T)` | `≥ T/6` for every `T ∈ ℕ` (no `T₀`) | explicit constant |
| LB16 | Theorem 35, statement | False as proved for large `η`: negative entropy, `d = 1000`, `η = 7`, `ε = 4η²/d = 0.196`: the uniform point is not an ε-minimizer (error `0.7329`), so the trajectory of the proof is invalid. For the proof's loss `𝟙 - e_d` the best ε-approximate trajectory (exact KL-ball dynamics) has long-run per-round regret `0.033` (`d = 1000`), `3.3e-5` (`d = 10⁶`); with rescaled losses `c(𝟙 - e_d)` the best constant is `≈ log(4η²)/η` (`0.76` at `η = 7`, `0.11` at `η = 100`, `0.015` at `η = 1000`, `d ≥ 10⁶`): with an absolute constant in `Ω(T)` the statement is unsupported, and likely false, as `η → ∞`. For general `ν` (worst case `r'' = c₁x^{-ν}`), on the grid, `error ≤ 4η²/(c₁d^ν)` still holds at `η = 2c₁d^{ν-1}/(3ν)` and fails at `η = 5c₁d^{ν-1}/(3ν)` (e.g. `ν = 3`, `c₁ = 0.1`, `d = 1000`) | assume `η ≤ c₁d^{ν-1}/(3ν)`; keep `ε ≥ 4η²/(c₁d^ν)` (the proof gives `(e/2)η²/(c₁d^ν)`) | false statement (of the proof's claim; missing hypothesis) |
| LB17 | Theorem 35, statement and proof | Loss range, initialization and regret constant not stated; the proof's `T - T/d` | constant losses `𝟙 - e_{i₀} ∈ [0,1]^d`, `a 0 = u₀`, regret `= T(1 - 1/d) ≥ T/2`; only `c₁` is used | explicit constant |
| LB18 | Theorem 36, statement | `k/(2η)`, `3k/(2η)` (phase lengths `3k/(2η)`, `k/η`) need not be integers | parametrize by `τ ∈ ℕ`, `k = 2ητ`; `k ≤ Tη/20` becomes `T ≥ 40τ` | typo |
| LB19 | Theorem 36, proof | Reuses Lemma 34 (LB6); no restriction on `η`. With this trajectory the error of staying exceeds `4ηe^{-ητ}` from `η ≈ 2.7` | assume `0 < η ≤ 1`; use Lemma 34.NE (both alternatives: in `[τ, 3τ)` the loss penalizes the small coordinate, in `[5τ, T)` it favours it) | missing hypothesis |
| LB20 | Theorem 36, statement and proof | "`ε = 4ηe^{-k/2}`", "regret `Ω(T)`"; the proof's last regret step ("this are `3T/4` steps") ignores the comparator's loss `2τ`; the statement omits what it is about (the exact trajectory keeps `≥ 1/2` on the optimal arm; balance `2τ`) and the start `(1/2,1/2)` (in the proof's summary only) | every `ε ≥ 4ηe^{-ητ}`, one trajectory; regret `≥ (T - 9τ)/2 ≥ T/3`; add conclusions (1), (2) of §1.4. The proof's other claims are right: `w_{4τ} = (1/2,1/2)` exactly, the last phase has `T - 5τ ≥ 7T/8 ≥ 3T/4` rounds | explicit constant |
| LB21 | Lean modelling (not a paper erratum) | Comparisons with boundary points use the junk `r 0` of a power barrier: existence statements for general barriers (Theorem 35, Lemma 34) are false in Lean, and Theorem 6 is vacuous for the log barrier | §1.5: barrier statements on `K° = {w ∈ Δ : ∀ i, 0 < w i}` (recommended), or `ContinuousOn r (Set.Icc 0 1)` | modelling |

Checked and correct: the identity `w_{4τ} = (1/2, 1/2)` of Theorem 36; `w_τ^1 ≤ e^{-ητ}` in Lemma 14
(indeed `≤ e^{-ητ}/(d-1)`); the balance of the losses of Lemma 14 (`= τ`); the appendix hypothesis
`(1/η)log(4η/ε) ≤ α` is `ε ≥ 4ηe^{-ηα}`; the threshold `4ηe^{-ηα}` itself is valid for `η ≤ 1`
(with margin: the trajectory is `(e/(d-1))η²e^{-ηα}`-approximate).

## 4. Numerical checks

Scripts in
`/tmp/claude-663481/-home-rdegenne-Documents-Lean-Schlisselberg2026Hidden/7ad2edfa-b559-4fea-932a-1aff1e8cf05b/scratchpad/lower-bounds/`
(scratchpad, not in the repository), each run with `python3 -I <script>`; outputs in
`out_*.txt` next to them. mpmath 1.4.1, 40–160 digits. The constructions are symmetric in the
non-distinguished coordinates, so points are stored as (mass, multiplicity) groups; the grouped
form is checked against full `d`-dimensional vectors and against the Lean definitions of
`negEntropy` and `bregDiv` (`validate_gibbs.py`). Exact steps are built with the MW recursion and
compared with the closed forms (relative error `≤ 1e-25`); their error is `0` by Lemma G (validated
numerically). The error of a stay step is computed in a cancellation-free form,
`log(1 + ∑_j w_j ψ(η(⟨ℓ,w⟩ - ℓ_j)))`, which matters when `ε` is as small as `e^{-10⁷}`. The
trajectories do not depend on `ε` and approximate steps are monotone in `ε`
(`IsApproxMirrorDescentStep.mono`), so "maximum error `≤` threshold" covers every `ε` at and above
the threshold.

- `nelib.py`: shared helpers (MW step, stable stay error, KL, Lean `negEntropy`/`bregDiv`).
- `validate_gibbs.py`: (1) on 20 800 comparison points (random positive `w`, `ℓ ∈ [0,1]^d`,
  `η ∈ {1e-3, 0.1, 1, 5}`, `d ∈ {2,3,5,10}`, random interior points, faces and vertices), `MW(w)`
  minimizes the Lean objective, `min φ = -log Z`, `φ(b) - φ(MW) = KL(b‖MW)`, and the stable stay
  error equals `φ(w) - φ(MW)` (difference `≤ 1.3e-50`); (2) `G_η(m)` and its bounds 34.NE-d on
  224 cases; (3) grouped vs full vectors on 216 steps. All pass.
- `check_lemma14_thm4.py`: Lemma 14 on `d ∈ {2,3,10,1000}`, `η ∈ {1e-4, 1e-3, 1e-2, 0.1, 0.3, 0.5,
  0.75, 1}`, `T ∈ {1, …, 12, 20, 31, 50, 100, 333, 1000, 10⁴, 10⁵, 10⁶}`, `α` in a grid of up to 12
  values of `[0, T/2]` (`0, 1/2, 1, 3/2, 2.999, 3, T/4, T/3, 0.45T, T/2 - 1/2, T/2 - 1e-9, T/2`;
  four for `T ≥ 10⁵`): every step valid at `ε = 4ηe^{-ηα}`, positivity, α-balance (`O(T)` scan),
  minimality of `i₁`, regret `≥ (T-2α)/2` and `≥ (1-1/d)(T-2α)`; Theorem 4 as `α = T/3` (regret
  `≥ T/6`). Also `η ∈ {1.5, …, 100}` to locate the failures, and Theorem 4⁺ (`η ∈ [1, 100]`, regret
  `≥ T/10`). Results: 6 624 points with `η ≤ 1`, 0 failures; maximum error/threshold `0.488`
  (attained for `d = 2`, `η = 1`, `α` just below an integer: `e(e - 2)/4`); minimum
  regret/((T - 2α)/2) `1.0` (tight: `T = 1`, `α = 0`, `d = 2`); MW closed forms to `4.7e-36`; the
  generic per-step KL error (`T ≤ 2000`) agrees. Theorem 4: 672 points, 0 failures, minimum
  regret/(T/6) `1.0001` (tight), maximum error/(4ηe^{-ηT/3}) `0.350`. Outside the range
  (7 452 points with `η > 1`): violations from `η = 1.5` (only for non-integer `α`), and for integer
  `α` from `η = 2.7`; at `η = 100` the ratio reaches `1.8e84`. Theorem 4⁺: 532 points
  (`η ∈ [1, 100]`, `T ≤ 3000`), 0 failures, minimum regret/T `0.1155` (`= tanh(1/2)/4`).
- `check_thm36.py`: `η` as above, `τ ∈ {0,1,2,3,5,10,30,100,1000,25000}`,
  `T ∈ {40τ, 40τ+1, 40τ+7, 100τ, 10⁶}`: 368 points with `η ≤ 1`, 0 failures; maximum error/threshold
  `0.180`; minimum regret/T `0.450` (claim `1/3`); closed forms (`a_τ`, `a_{4τ} = u₀`, `a_{5τ}`) to
  `1.7e-47`; exact trajectory `≥ 1/2` on `i₁`; balance `2τ`. Outside the range the error exceeds the
  threshold from `η = 2.7` (`η = 2.6`: ratio `0.948`).
- `check_thm35.py`: worst-case barriers `r'' = c₁x^{-ν}` (negative entropy, Tsallis, log barrier
  are of this form) and the non-monotone `r'' = c₁x^{-ν}(1.5 + 0.5 cos(20 log x))`, `ν ∈ {1, 1.25,
  1.5, 2, 3, 5, 8}`, `c₁ ∈ {0.1, 1, 10}`, `d ∈ {2,3,10,1000}`, `η/η_max ∈ {1e-6, …, 1}` and
  absolute `η ∈ {1e-4, 1e-2, 1, 100}` when `≤ η_max = c₁d^{ν-1}/(3ν)`: 1 482 points, 0 failures;
  maximum error/(4η²/(c₁d^ν)) `0.141`, maximum error/((e/2)η²/(c₁d^ν)) `0.416`. The symmetric
  reduction of the supremum is checked on 27 000 random points (`d = 3`). Out of range: no violation
  at `η = 2η_max`, violations from `η = 5η_max`; negative entropy `d = 1000`, `η = 7`: error `0.7329`
  vs `ε = 0.196` (closed form agrees). The regret of the constant trajectory is `T(1 - 1/d)`.
- `check_thm35_large_eta.py`: the exact best ε-approximate trajectory for the losses `c(𝟙 - e_{i₀})`
  (negative entropy, `ε = 4η²/d`) through the KL-ball dynamics `kl(p_{t+1}‖M(p_t)) ≤ ε` (greedy is
  optimal by monotonicity). Long-run per-round regret: `c = 1`: `0.033` (`η = 7, d = 1000`), `3.3e-5`
  (`d = 10⁶`); best `c`: `0.759` (`η = 7`), `0.369` (`η = 20`), `0.106` (`η = 100`), `0.0175`/`0.015`
  (`η = 1000`, `d = 10⁶`/`10⁹`), matching `log(4η²)/η`.
- `check_lemma34_lemma24.py`: the counterexamples LB6 (a)–(c) and LB1; Lemma 34′ on power barriers
  (`ν ∈ {1,1.5,2,3,5}`, `c₁ ∈ {0.1,1}`, `d ∈ {2,3,6}`, `m ∈ [1e-6, 0.95]`, losses constant off `i₀`,
  random `w`, `η/η_max(m) ∈ {1e-4, 0.01, 0.3, 1}`) with the exact error (inner minimization over the
  other coordinates by KKT); corrected Lemma 24 on random ε-steps. Results: LB6 (a) error
  `4.0015 > 0.1`, (b) `0.9078 > 0.04`, (c) log barrier: error/ε up to `177.7` (`η = 100`,
  `w^1 = 0.03`); Lemma 34′: 3 360 cases, 0 failures, maximum error/(2η²m^ν/c₁) `0.283`; LB1:
  `|Δ| = 4.503e-5` against the paper's `3.233e-5` and the corrected `4.572e-5`; corrected
  Lemma 24 on 14 860 random coordinates of random ε-steps (`η ∈ [1e-3, 3.2]`, `ε ∈ [1e-8, 0.1]`,
  losses in `[-1,1]^d`): maximum `|Δ|`/bound `0.903`.
- `check_lemma35A.py`: Lemma 35.A directly (both sides `y < x`, `y > x`) for the two barrier
  families, `ν ∈ {1, 1.5, 2, 3, 5, 8}`, `c₁ ∈ {0.1, 1, 10}`, `x ∈ [1e-6, 0.95]`,
  `η/η_max(x) ∈ {1e-3, 0.1, 0.5, 1}`: 1 008 cases, 0 failures, maximum sup/bound `0.417`.
- `boundary_junk.py`: LB21 (`bregDiv (-log) e_0 u₀ = -d log d` in Lean).

## 5. Open points

- Lemma 14 for `η > 1` is not claimed: the stuck mechanism fails there, and I did not find a clean
  replacement (exact steps on alternating losses give regret `∝ αT`, not `∝ T - 2α`, when `α < 1`).
- Theorem 35 with an absolute constant for large `η`: evidence (LB16) that it fails, not a proof
  (only the loss family `c(𝟙 - e_{i₀})` was searched).
- The boundary decision of §1.5 is cross-cutting (Theorems 6, 35, Lemma 34) and is the caller's.
