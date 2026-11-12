# Explicit constants: negative-entropy upper bounds on the simplex (area A)

Corrected, fully explicit statements of [SSKM26, Lemma 15], [SSKM26, Theorem 5] and
[SSKM26, Theorem 7] (arXiv:2511.22283v2), a blueprint of their proofs in which every constant is
derived, the errata found on the way and the numerical checks. Written 2026-11-12. Conventions:
`notes/modelling.md` (Lean rounds from `0`, `a 0 = w_1`, regret over the rounds `t < T`,
ε-approximate steps, positive iterates, one-sided α-balance relative to a minimiser `i*`).

**Summary of the changes with respect to v2.**
- Lemma 15 and Theorem 5: uniform initialisation added (Theorem 7 states it). All three: the
  comparator term `D_R(w, w_1)/η` becomes `log d / η` (`= D_R(w*, w_1)/η`, all the proof gives);
  `O(·)` becomes an explicit constant.
- Lemma 15: threshold `e^{-ηα} min{η⁴, T⁻²} / (100 d)` (v2: `min{η⁴, T⁻²} / (d max{6e^{ηα}, 1/η})`):
  the constant `6` is replaced by `100`, the `1/η` branch disappears (new proof of Lemma 39),
  `T ≥ 3` is dropped.
- Theorem 5: losses in `[0, 1]^d` (user decision; false for `[-1, 1]^d`), threshold
  `e^{-ηT/2} min{η⁴, T⁻²} / (100 d)` (v2: `/(6d)`), `T ≥ 3` dropped.
- Theorem 7: `T ≥ 256 log d` (v2: `T ≥ 256`), `ε ≤ δ / (6 d³ T⁴)` (v2: `δ / (6 d² T⁴)`),
  conclusion `Regret ≤ 2 √(T log d)`.
- The proof is reorganised: no exact trajectory (Lemmas 10, 11 are replaced by a direct one-step
  bound), no sets `S_t` (Lemmas 37, 38 are not needed), and Lemma 39 has a new, three-line proof
  (moving towards the vertex `e_{i*}` costs a Bregman divergence controlled by `1/a^{i*}` only).

Contents: §1 statements, §2 blueprint, §3 errata, §4 numerical checks, §5 open points.

## 1. Corrected statements

### 1.0 Common setting

- `α` a finite nonempty type, `d = Fintype.card α`, `Δ = simplex α`, `ū = fun _ ↦ 1 / d`.
- `⟨x, y⟩ = ∑ k, x k * y k`; `e j = Pi.single j 1`.
- `D x y = ∑ k, (x k * log (x k / y k) - x k + y k)`: for `y` with positive coordinates this is
  `bregDiv negEntropy x y (F' y)` with `F' y h = ∑ k, log (y k) * h k`, LMLExplore's `negEntropy`
  (and also the Bregman divergence of the paper's `∑ x log x`); on `Δ × Δ` it is the relative
  entropy `∑ k, x k * log (x k / y k)`.
- `x` is an **ε-step from `a` for the loss `ℓ`** (learning rate `η`): `x ∈ Δ` and
  `∀ b ∈ Δ, η ⟨ℓ, x⟩ + D x a ≤ η ⟨ℓ, b⟩ + D b a + ε` (modelling.md, with `K = Δ`, `F = negEntropy`).
- **Trajectory hypotheses** for `a : ℕ → α → ℝ`, losses `ℓ : ℕ → α → ℝ`, horizon `T : ℕ`:
  - (T1) `a 0 = ū`;
  - (T2) `∀ t ≤ T, ∀ k, 0 < a t k` (positivity, including the last iterate `a T`);
  - (T3) `∀ t < T, a (t + 1)` is an ε-step from `a t` for `ℓ t`.
- `regret ℓ a u T = ∑ t < T, (⟨ℓ t, a t⟩ - ⟨ℓ t, u⟩)`; `L s t i = ∑ r ∈ Finset.Ico s t, ℓ r i`.
- In `min (η ^ 4) (1 / T ^ 2)` the horizon is cast to `ℝ`; for `T = 0` it is `0` (Lean's
  `1 / 0 = 0`) and every statement is trivial (the regret is an empty sum).

### 1.1 Lemma 15 (corrected)

Hypotheses:
- `0 < η`, `η ≤ 1/16`;
- `∀ t < T, ∀ k, |ℓ t k| ≤ 1`;
- `i* : α` with `∀ i, L 0 T i* ≤ L 0 T i` (a best arm), and `A : ℝ` with the α-balance
  `∀ s t, s ≤ t → t ≤ T → ∀ i, L s t i* - L s t i ≤ A`;
- (T1), (T2), (T3);
- `ε ≤ exp (-(η * A)) * min (η ^ 4) (1 / T ^ 2) / (100 * d)`.

Conclusion: `∀ u ∈ Δ, regret ℓ a u T ≤ log d / η + η * T`.

(`A ≥ 0` follows from the balance with `s = t`. `T ≥ 3` is not needed. The minimality of `i*` is
used only in the last step, to pass from the comparator `e i*` to every `u ∈ Δ`.)

### 1.2 Theorem 5 (corrected)

Hypotheses:
- `0 < η`, `η ≤ 1/16`;
- `∀ t < T, ∀ k, ℓ t k ∈ Set.Icc 0 1` (losses in `[0, 1]^d`);
- (T1), (T2), (T3);
- `ε ≤ exp (-(η * T / 2)) * min (η ^ 4) (1 / T ^ 2) / (100 * d)`.

Conclusion: `∀ u ∈ Δ, regret ℓ a u T ≤ log d / η + η * T`.

### 1.3 Theorem 7 (corrected)

Hypotheses:
- a probability space `(Ω, P)`; losses `ℓ : ℕ → Ω → α → ℝ` with `∀ t, Measurable (ℓ t)`,
  `iIndepFun ℓ P`, `∀ t, IdentDistrib (ℓ t) (ℓ 0) P P` (only "independent over the rounds, same
  mean vector" is used), and `∀ t ω k, ℓ t ω k ∈ Set.Icc (-1) 1`;
- `0 < δ`, `δ ≤ 1`;
- `256 * log d ≤ T` (equivalently `η ≤ 1/16`);
- `η = √(log d / T)`;
- `ε ≤ δ / (6 * d ^ 3 * T ^ 4)`.

Conclusion: there is a measurable `E ⊆ Ω` with `1 - δ ≤ P.real E` such that for every `ω ∈ E` and
every `a` satisfying (T1), (T2), (T3) for the losses `fun t ↦ ℓ t ω`:
`∀ u ∈ Δ, regret (fun t ↦ ℓ t ω) a u T ≤ 2 * √(T * log d)`.

`d = 1` is allowed (then `η = 0`, the simplex is a point and the regret is `0`). `E` does not
depend on `ε`, on the trajectory or on `u`.

Variants (all proved by the same blueprint, §2.8; pick one for the formalisation):
- (7a) the same with `ε ≤ √δ / (500 * d ^ 3 * T ^ 3)` (weaker hypothesis; implies the above);
- (7b) without the hypothesis on `T`, with conclusion `≤ 32 * √(T * log d)` (if `T < 256 log d`
  then `√(T log d) > T/16` and the regret is at most `2T` for any trajectory);
- (7c) under the extra hypothesis `d ≤ T`: `ε ≤ δ / (1000 * d ^ 2 * T ^ 4)` suffices (the paper's
  `d²`, other constant).

### 1.4 Deviations from v2 and their errata

| statement | v2 | corrected | erratum |
|---|---|---|---|
| L15, T5, T7 | comparator `D_R(w, w_1)/η` | `log d / η` | A3 |
| L15, T5 | initialisation not stated | `a 0 = ū` | A2 |
| L15, T5 | `O(Tη)` | `Tη` | A14, A15 |
| L15 | `ε ≤ min{η⁴,T⁻²}/(d max{6e^{ηα},1/η})` | `ε ≤ e^{-ηα} min{η⁴,T⁻²}/(100d)` | A14 |
| L15, T5 | `T ≥ 3` | none | A14, A15 |
| T5 | losses in `[-1, 1]^d` | `[0, 1]^d` | A1 |
| T5 | `ε ≤ e^{-ηT/2} min{η⁴,T⁻²}/(6d)` | `/(100 d)` | A15 |
| T7 | `T ≥ 256` | `T ≥ 256 log d` | A16 |
| T7 | `ε ≤ δ/(6d²T⁴)` | `ε ≤ δ/(6d³T⁴)` | A16 |
| T7 | `O(√(T log d))` | `2√(T log d)` | A16 |

## 2. Blueprint

Names reuse the paper's numbers; a primed or lettered name is a variant of the paper's lemma. All
lemmas are about a fixed `η`, `ε`, `T`, `ℓ`, `a` in the setting of §1.0, and all assume
`a 0 ∈ Δ` (implied by (T1)), so that with (T3) `a t ∈ Δ` for every `t ≤ T` (used in L24 through
`∑ k, a t k = 1`, and in L27, L39). If `T ≥ 1`, (T3) forces `0 ≤ ε` (take `b = a 1`). Throughout,
`g t = fun k ↦ η * ℓ t k + log (a (t + 1) k) - log (a t k)` for `t < T` (the gradient of the
round-`t` objective at `a (t + 1)`), and the **balance** (Definition 32, with `r' = log`; the `+1`
of `r(x) = x log x` cancels) is

`B j i s t = (log (a s j) - log (a t j)) + (log (a t i) - log (a s i))`.

Scalar Bregman divergence: `Dr x y = x * log (x / y) - x + y` for `x ≥ 0`, `y > 0` (at `x = 0`
it is `y`), so `D x y = ∑ k, Dr (x k) (y k)`.

### 2.1 Scalar facts (entropy form of Lemma 21)

**L21a (χ² upper bound).** `0 ≤ x`, `0 < y` ⟹ `Dr x y ≤ (x - y) ^ 2 / y`.
Proof: `log z ≤ z - 1` with `z = x / y` gives `x log (x/y) ≤ x (x - y)/y` (also for `x = 0`), so
`Dr x y ≤ x(x - y)/y - x + y = (x - y)²/y`.

**L21b (lower bound).** `0 ≤ x ≤ y`, `0 < y` ⟹ `(y - x) ^ 2 / (2 * y) ≤ Dr x y`.
Proof: `Dr x y = ∫ₓʸ (z - x)/z dz ≥ (1/y) ∫ₓʸ (z - x) dz`; or, with `s = x/y ∈ [0, 1]`,
`h(s) = s log s - s + 1 - (1 - s)²/2` has `h(1) = 0` and `h'(s) = log s + 1 - s ≤ 0` on `(0, 1]`,
so `h ≥ 0` on `(0, 1]`; at `s = 0`, `Dr 0 y = y ≥ y/2`.

**L21c (monotonicity).** For `y > 0`, `x ↦ Dr x y` is antitone on `[0, y]` and monotone on
`[y, ∞)` (derivative `log (x / y)`), and `Dr x y ≥ 0`.

(The paper's Lemma 21 bounds `D` by `β/2 ‖·‖²` with `β` the maximum of `r''` on the segment; that
maximum is `2^ν` times the claimed one on the segment of Lemma 11 (erratum A7) and infinite on the
segment of Lemma 39 (erratum A12). L21a needs only the base point `y` and holds on the whole
segment, endpoints with zero coordinates included.)

### 2.2 One step

**L26 (three-point identity).** For `F` with derivatives `F'y`, `F'z` at `y`, `z`:
`D_F x z - D_F x y - D_F y z = (F'y - F'z) (x - y)`. Pure algebra (as in the paper).

**L26′ (objective identity; characterisation of ε-steps).** For `t < T` under (T2) and every
`x ∈ Δ`, with `φ x = η ⟨ℓ t, x⟩ + D x (a t)`:
`φ x - φ (a (t + 1)) = ⟨g t, x - a (t + 1)⟩ + D x (a (t + 1))`.
Hence (T3) at `t` is equivalent to: `a (t + 1) ∈ Δ` and
`∀ x ∈ Δ, ⟨g t, x - a (t + 1)⟩ + D x (a (t + 1)) ≥ -ε`.
Proof: L26 with `(x, y, z) = (x, a (t + 1), a t)`. (Remark, not used: `φ x - min φ` is the relative
entropy of `x` from the exact Hedge update, so the ε-steps are exactly the points of `Δ` at
relative entropy `≤ ε` from the exact update; the numerical checks use this.)

**L22 (approximate first-order condition; corrected form, the one used).** `t < T`, (T2), (T3),
`h : α → ℝ` with `a (t + 1) + h ∈ Δ`, `0 < u ≤ 1`. Then
`⟨g t, h⟩ ≥ -ε / u - u * ∑ k, h k ^ 2 / a (t + 1) k`.
Proof: `x = a (t + 1) + u • h ∈ Δ` (convex combination of `a (t + 1)` and `a (t + 1) + h`). By L26′,
`u ⟨g t, h⟩ + D x (a (t + 1)) ≥ -ε`, and by L21a coordinatewise
`D x (a (t + 1)) ≤ u² ∑ k, h k² / a (t + 1) k`. Divide by `u`.
(Optimising `u` gives the paper's form `⟨g, h⟩ ≥ -2 max{√(εQ), ε}`, `Q = ∑ h²/a(t+1)`, with the
sign of the second case corrected, erratum A6; the blueprint always picks `u` explicitly.)

**L23 (quadratic).** `0 < p`, `0 ≤ q`, `0 ≤ c`, `p x² - q x - c ≤ 0` ⟹ `x ≤ q / p + √(c / p)`.
Proof: if `x > x₀ := q/p + √(c/p)` then `x ≥ 0` and
`p x² - q x = x (p x - q) > x₀ · p √(c/p) = x₀ √(pc) ≥ √(c/p) √(pc) = c`.

**L24 (max step; corrected constant).** `t < T`, (T2), (T3), `∀ k, |ℓ t k| ≤ 1`, `i` with
`a (t + 1) i ≤ a t i`. Then
`a t i - a (t + 1) i ≤ 4 * η * a t i + √(2 * ε * a t i)`.
Proof. Write `a = a t`, `â = a (t + 1)`, `Δ = a i - â i`; assume `Δ > 0`. Let
`I⁺ = {k | â k > a k}` and `P = ∑ k ∈ I⁺, (â k - a k)`. Since `∑ k, (â k - a k) = 0` and `i ∉ I⁺`,
`P = ∑ k ∉ I⁺, (a k - â k) ≥ Δ`; put `λ = Δ / P ∈ (0, 1]`. Define `w̃ i = a i`,
`w̃ k = â k - λ (â k - a k)` for `k ∈ I⁺`, `w̃ k = â k` otherwise. Then:
- `w̃ ∈ Δ` (coordinates `≥ 0`: for `k ∈ I⁺`, `w̃ k ≥ a k > 0`; sum `1 + Δ - λ P = 1`);
- `‖â - w̃‖₁ = Δ + λ P = 2Δ`, so `η ⟨ℓ t, â - w̃⟩ ≥ -2 η Δ` (Hölder, `|ℓ t k| ≤ 1`);
- `D â a - D w̃ a ≥ Dr (â i) (a i) ≥ Δ² / (2 a i)`: the `i` term is `Dr (â i) (a i) - 0` and L21b;
  for `k ∈ I⁺`, `w̃ k ∈ [a k, â k]` so `Dr (w̃ k) (a k) ≤ Dr (â k) (a k)` (L21c); other terms equal.

(T3) with `b = w̃`: `ε ≥ η ⟨ℓ t, â - w̃⟩ + D â a - D w̃ a ≥ Δ²/(2 a i) - 2ηΔ`. L23 with
`p = 1/(2 a i)`, `q = 2η`, `c = ε`: `Δ ≤ 4 η a i + √(2 ε a i)`. ∎
(The symmetric statement for `a (t + 1) i ≥ a t i`, with `a (t + 1) i` in place of `a t i`, has the
same proof with `I⁻`; it is not used. The paper's `√(ε/h)` is false, erratum A4. The proportional
`w̃` replaces the paper's prefix construction `S, i'`, which is harder to formalise.)

**L25 (not too far, forward; corrected hypothesis).** Hypotheses of L24 without the order
condition, plus `η ≤ 1/16` and `ε ≤ a t i / 32`. Then `a t i / 2 ≤ a (t + 1) i`.
Proof: trivial if `a (t + 1) i ≥ a t i`; otherwise by L24,
`a t i - a (t + 1) i ≤ 4 (1/16) a t i + √(2 (a t i / 32) a t i) = a t i / 4 + a t i / 4`. ∎
(Only this forward direction is used, once, in L40. The backward direction of the paper is not
needed.)

### 2.3 Balance

**L29 (transitivity).** `B j i s t = ∑ r ∈ Finset.Ico s t, B j i r (r + 1)` for `s ≤ t`
(telescoping).

**L33a (one-step balance).** `t < T`, (T2), (T3), `i ≠ j`, `0 < v ≤ a (t + 1) i`. Then
`B j i t (t + 1) ≤ η * (ℓ t j - ℓ t i) + ε / v + v * (1 / a (t + 1) j + 1 / a (t + 1) i)`.
Proof: write `â = a (t + 1)`. L22 with `h = â i • (e j - e i)` (`â + h ∈ Δ`: coordinate `i` becomes
`0`, `j` becomes `â j + â i`) and `u = v / â i ∈ (0, 1]`: `∑ h k²/â k = â i² (1/â j + 1/â i)` and
`⟨g t, h⟩ = â i (g t j - g t i)`, so `g t j - g t i ≥ -ε/v - v (1/â j + 1/â i)`. Finally
`B j i t (t + 1) = η (ℓ t j - ℓ t i) - (g t j - g t i)` by definition of `g t`. ∎

**L33 (balance over an interval; corrected Lemma 33, budget form used in L40).** (T2), (T3),
`1 ≤ T`, `0 < ψ`, `ε ≤ ψ / (8 * T ^ 2)`, `s ≤ t ≤ T`, `i, j : α`, and
`∀ r, s < r → r ≤ t → ψ ≤ a r i ∧ ψ ≤ a r j`. Then
`B j i s t ≤ η * (L s t j - L s t i) + (t - s) / T ≤ η * (L s t j - L s t i) + 1`.
Proof: `i = j`: both balances are `0`. Otherwise L29 and, for each `r ∈ Ico s t`, L33a with
`v = ψ / (4T)` (`≤ ψ ≤ a (r + 1) i`): the error is
`ε/v + v (1/a(r+1) j + 1/a(r+1) i) ≤ 4Tε/ψ + (ψ/(4T)) (2/ψ) ≤ 1/(2T) + 1/(2T) = 1/T`. ∎

**L33′ (paper-shaped corrected Lemma 33).** Same hypotheses with `0 < ε ≤ 2ψ` instead of the
budget: `B j i s t ≤ η (L s t j - L s t i) + (t - s) √(8 ε / ψ)`. Proof: L33a with
`v = √(εψ/2) ≤ ψ`. (v2 claims `(t - s) √(ε/ψ)`, which is false, erratum A8; the sharp one-step
constant is `2√(ε/ψ)` asymptotically, §4 check 4.)

**L13 (balance to coordinate bounds; entropy).** For `s, t ≤ T` with (T2), and `K : ℝ`:
1. `a s i ≤ a t i` and `B j i s t ≤ K` ⟹ `a s j ≤ exp K * a t j`;
2. `a t j ≤ a s j` and `B j i s t ≤ K` ⟹ `a t i ≤ exp K * a s i`.
Proof: in 1, `log (a t i) - log (a s i) ≥ 0`, so `log (a s j) - log (a t j) ≤ K`; take `exp`. In 2
symmetrically. ∎

### 2.4 The best arm stays away from zero (Lemma 40, corrected)

**L40.** Hypotheses: (T1), (T2), (T3); `1 ≤ T`; `0 ≤ η ≤ 1/16`; `∀ t < T, ∀ k, |ℓ t k| ≤ 1`;
`j : α` and `A : ℝ` with `∀ s t, s ≤ t → t ≤ T → ∀ i, L s t j - L s t i ≤ A`; with
`ξ = exp (-(η * A + 1)) / d`, `ε ≤ ξ / (32 * T ^ 2)`. Conclusion: `∀ t ≤ T, ξ ≤ a t j`.
(`j` need not be a best arm.)

Proof. Note `ξ < 1/d` and `ε ≤ ξ/32` (as `T ≥ 1`). Strong induction on `t ≤ T`. `t = 0`:
`a 0 j = 1/d ≥ ξ`. Let `1 ≤ t ≤ T` and `∀ s < t, ξ ≤ a s j`.
- Case 1: `a s j ≤ a t j` for some `s < t`: then `ξ ≤ a t j`.
- Case 2: `∀ i ≠ j, a t i ≤ 1/d`: then `a t j = 1 - ∑ i ≠ j, a t i ≥ 1/d ≥ ξ`.
- Case 3: `∀ s < t, a t j < a s j`, and some `i ≠ j` has `a t i > 1/d`. Fix this `i`.
  - (a) L25 at round `t - 1` (`ε ≤ ξ/32 ≤ a (t-1) j / 32`): `a t j ≥ a (t-1) j / 2 ≥ ξ/2`.
    So `∀ r ≤ t, ξ/2 ≤ a r j`.
  - (b) Claim: `∀ s ≤ t, ξ < a s i`. Otherwise let `s` be the largest `s ≤ t` with `a s i ≤ ξ`;
    `s < t` since `a t i > 1/d > ξ`, and `a r i > ξ` for `s < r ≤ t`. L33 with `ψ = ξ/2`
    (`ε ≤ ξ/(32T²) ≤ ψ/(8T²)`; for `s < r ≤ t`: `a r i > ξ ≥ ψ`, `a r j ≥ ψ` by (a)) and the
    balance: `B j i s t ≤ η A + 1`. As `a t j < a s j` (Case 3), L13.2 gives
    `a t i ≤ e^{ηA+1} a s i ≤ e^{ηA+1} ξ = 1/d`, contradicting `a t i > 1/d`.
  - (c) L33 on `[0, t]` with `ψ = ξ/2` (for `0 < r ≤ t`: `a r i > ξ` by (b), `a r j ≥ ψ` by (a)):
    `B j i 0 t ≤ η A + 1`. As `a t i > 1/d = a 0 i`, L13.1 gives
    `1/d = a 0 j ≤ e^{ηA+1} a t j`, i.e. `ξ ≤ a t j`. ∎

(v2 assumes `ε ≤ ξ/(2T²)`; with the corrected Lemmas 25 and 33 its proof needs `ε ≤ ξ/32` and
`ε ≤ ξ/(16T²)`; erratum A13.)

### 2.5 Regret (Lemmas 27 and 39)

**L27 (OMD helper; Pinsker).** `x, y ∈ Δ`, `y` positive, `0 < η`, `∀ k, |ℓ k| ≤ 1`:
`⟨ℓ, y - x⟩ ≤ D x y / η + η / 2`.
Proof: `⟨ℓ, y - x⟩ ≤ ‖y - x‖₁ ≤ ‖y - x‖₁²/(2η) + η/2` and `D x y ≥ ‖x - y‖₁²/2` (Pinsker, i.e. the
1-strong convexity of `negEntropy` on `Δ` for `ℓ¹`: LMLExplore's `strongConvexOn_negEntropy`).
(Fallback without Pinsker: LMLExplore's `sum_sub_mul_sub_sum_mul_log_div_div_le` gives the bound
`(e^η - 1 - η)/η ≤ 0.511 η` for `η ≤ 1/16`; see the remark after L39.)

**L39 (regret when the best arm stays away from zero; corrected statement, new proof).**
Hypotheses: (T2), (T3); `0 < η ≤ 1`; `∀ t < T, ∀ k, |ℓ t k| ≤ 1`; `j : α`, `0 < ξ ≤ 1` with
`∀ t, 1 ≤ t → t ≤ T → ξ ≤ a t j`; `ε ≤ η ^ 4 * ξ / 16`. Conclusion:
`∑ t < T, (⟨ℓ t, a t⟩ - ℓ t j) ≤ -log (a 0 j) / η + η * T`;
if moreover `∀ i, L 0 T j ≤ L 0 T i`, then `∀ u ∈ Δ, regret ℓ a u T ≤ -log (a 0 j) / η + η * T`,
and with (T1) the right-hand side is `log d / η + η T`.

Proof. Fix `t < T`, write `â = a (t + 1)`.
1. (Vertex direction.) L22 with `h = e j - â` (`â + h = e j ∈ Δ`) and `u = η² ξ / 4 ∈ (0, 1]`:
   `∑ k, h k²/â k = ∑ k ≠ j, â k + (1 - â j)²/â j = (1 - â j)/â j ≤ 1/ξ`, so
   `⟨g t, e j - â⟩ ≥ -4ε/(η²ξ) - η²/4 ≥ -η²/4 - η²/4 = -η²/2`.
2. (Three points.) `⟨g t, e j - â⟩ = η ⟨ℓ t, e j - â⟩ + ⟨log â - log (a t), e j - â⟩` and by L26
   (`(x, y, z) = (e j, â, a t)`) the second term is `D (e j) (a t) - D (e j) â - D â (a t)`. Hence
   `η ⟨ℓ t, â - e j⟩ ≤ η²/2 + D (e j) (a t) - D (e j) (a (t + 1)) - D (a (t + 1)) (a t)`.
3. Sum over `t < T`, telescope, drop `-D (e j) (a T) ≤ 0`, and use `D (e j) (a 0) = -log (a 0 j)`:
   `η ∑ t < T, ⟨ℓ t, a (t + 1) - e j⟩ ≤ T η²/2 - log (a 0 j) - ∑ t < T, D (a (t + 1)) (a t)`.
4. L27 with `x = a (t + 1)`, `y = a t` for each `t < T`, summed:
   `∑ t < T, ⟨ℓ t, a t - a (t + 1)⟩ ≤ ∑ t < T, D (a (t + 1)) (a t) / η + η T / 2`.
   Adding 3 (divided by `η`) and 4: `∑ t < T, ⟨ℓ t, a t - e j⟩ ≤ -log (a 0 j)/η + ηT/2 + ηT/2`.
5. If `j` is a best arm, `⟨L 0 T, u⟩ ≥ L 0 T j` for `u ∈ Δ`, so
   `regret ℓ a u T ≤ ∑ t < T, (⟨ℓ t, a t⟩ - ℓ t j)`. With (T1), `-log (a 0 j) = log d`. ∎

Remark (fallback for L27). If L27 is formalised with the exponential bound `0.511 η` (valid for
`η ≤ 1/16`), take `u = η²ξ/6` in step 1 under `ε ≤ η⁴ξ/36`: the error is `≤ η²/3` per round and the
total `(1/3 + 0.511) ηT < ηT`. The threshold of L15 implies `ε ≤ η⁴ξ/36` too (`36e = 97.9 ≤ 100`).

### 2.6 Lemma 15

Proof of §1.1. If `T = 0` the regret is `0 ≤ log d / η`. Let `T ≥ 1` and
`ξ = exp (-(η A + 1)) / d ∈ (0, 1]`. From the threshold and `32 e ≤ 87 ≤ 100`:
`ε ≤ e^{-ηA} / (100 d T²) ≤ e^{-ηA-1} / (32 d T²) = ξ / (32 T²)`, so L40 (with `j = i*`) gives
`ξ ≤ a t i*` for all `t ≤ T`. From the threshold and `16 e ≤ 44 ≤ 100`:
`ε ≤ e^{-ηA} η⁴ / (100 d) ≤ η⁴ ξ / 16`, so L39 (with `j = i*`, `η ≤ 1/16 ≤ 1`) gives
`regret ℓ a u T ≤ log d / η + η T`. ∎

### 2.7 Theorem 5

**L5a (balance of losses in `[0, 1]^d`).** `∀ t < T, ∀ k, ℓ t k ∈ [0, 1]`, `i*` a best arm. Then
for `s ≤ t ≤ T` and every `i`: `L s t i* - L s t i ≤ min (t - s) (T - (t - s)) ≤ T / 2`.
Proof: every term `ℓ r i* - ℓ r i ≤ 1`, so the left side is `≤ t - s`. Also
`L s t i* - L s t i = (L 0 T i* - L 0 T i) - (L 0 s i* - L 0 s i) - (L t T i* - L t T i)` and the
first bracket is `≤ 0`, each term of the other two is `≥ -1`: `≤ s + (T - t)`. And
`min (a, T - a) ≤ T/2`. ∎ (For losses in `[-1, 1]^d` the bound is `T`, attained, §4 check 7.)

Proof of §1.2. Pick a best arm `i*` (finite nonempty `α`), apply L5a and L15 with `A = T/2`
(`[0, 1] ⊆ [-1, 1]`). ∎

### 2.8 Theorem 7

Write `N = d² (T + 1)²` and `A = √(2 T log (N / δ))` (for `T ≥ 1`, `δ ≤ 1`: `N/δ ≥ 4`, so `A > 0`).

**L7a (balance of i.i.d. losses w.r.t. the empirical best arm).** Hypotheses of §1.3 on `ℓ`, `δ`,
and `T ≥ 1`. Let `E = {ω | ∀ i j s t, s ≤ t → t ≤ T → Z i j s t ω < A}` with
`Z i j s t = (L s t i - L s t j) - ((t - s)/T) (L 0 T i - L 0 T j)` (losses `ℓ · ω`). Then `E` is
measurable, `P.real E ≥ 1 - δ`, and for `ω ∈ E`, every best arm `i*` of `ℓ · ω`, every `i` and
`s ≤ t ≤ T`: `L s t i* - L s t i ≤ A`.
Proof.
1. `Z i j s t = ∑ r < T, c r (ℓ r i - ℓ r j)` with `c r = 𝟙[s ≤ r < t] - p`,
   `p = (t - s)/T ∈ [0, 1]`.
   Its mean is `0`: `E[ℓ r i - ℓ r j] = μ i - μ j` for every `r` (identical distribution) and
   `∑ r < T, c r = (t - s) - T p = 0`.
2. (Hoeffding.) The `Y r = c r (ℓ r i - ℓ r j) ∈ [-2|c r|, 2|c r|]` are independent; by Hoeffding's
   lemma (`hasSubgaussianMGF_of_mem_Icc`) `Y r - E Y r` is sub-Gaussian with parameter `4 c r²`, and
   `∑ r, 4 c r² = 4 T p (1 - p) ≤ T`. Hoeffding (`measure_sum_ge_le_of_iIndepFun`):
   `P (Z i j s t ≥ A) ≤ exp (-A² / (2T)) = δ / N`.
3. Union bound over the `≤ d² (T + 1)²` tuples `(i, j, s, t)`: `P (Eᶜ) ≤ δ`.
4. On `E`, with `p = (t - s)/T ≥ 0` and `L 0 T i* - L 0 T i ≤ 0`:
   `L s t i* - L s t i = Z i* i s t + p (L 0 T i* - L 0 T i) ≤ Z i* i s t < A`. ∎

(The "bridge" `Z` removes the drift of the random arm `i*`: no mean appears on `E`. Its
sub-Gaussian parameter is `4 T p (1 - p) ≤ T`, against `4 (t - s) ≤ 4T` for the centred plain
interval sum `(L^i - L^j)_[s,t)`; the plain route also needs a second deviation to bound the drift
`(t - s)(μ^{i*} - μ^i)` through the optimality of `i*`, and gives `α = 2 √(8 T log (N/δ))`, i.e.
`16` times more in `α²`; erratum A16. Degenerate tuples (`s = t`, or `(s, t) = (0, T)`, or `i = j`)
have `Z = 0 < A` and need no Hoeffding: Mathlib's bound with a zero parameter is vacuous.)

**L7b (arithmetic).** `d ≥ 2`, `T ≥ 256 log d`, `0 < δ ≤ 1`, `η = √(log d / T)`:
1. `0 < η ≤ 1/16` and `T ≥ 256 log 2 > 177`;
2. `η A = √(2 log d · log (N/δ)) ≤ log d + log (N/δ) / 2 = log (d² (T + 1) / √δ)` (AM–GM), so
   `e^{-ηA} ≥ √δ / (d² (T + 1)) ≥ √δ / (2 d² T)`;
3. `min (η⁴, T⁻²) = min (log² d, 1) / T² ≥ (log 2)² / T² ≥ 0.48 / T²`;
4. hence `e^{-ηA} min (η⁴, T⁻²) / (100 d) ≥ 0.48 √δ / (200 d³ T³) ≥ √δ / (417 d³ T³)`, and
   `√δ / (417 d³ T³) ≥ δ / (6 d³ T⁴)` because `6 T ≥ 417 √δ` (`T > 177`, `δ ≤ 1`).

Proof of §1.3. If `d = 1`: `Δ = {ū}`, every regret is `0` (take `E = Ω`). If `d ≥ 2`, take `E`
from L7a. For `ω ∈ E`, pick a best arm `i*`; by L7a the losses are `A`-balanced w.r.t. `i*`; by
L7b.4 the hypothesis on `ε` implies the threshold of L15 with this `A`; L15 (with L7b.1) gives
`regret ≤ log d / η + η T = √(T log d) + √(T log d)`. ∎
Variants: (7a) uses L7b.4 before its last inequality (with `500 ≥ 417`); (7b) adds the trivial case
`T < 256 log d` (`regret ≤ 2T < 32 ηT = 32 √(T log d)`); (7c) under `T ≥ d`:
`3 (log d)² ≤ (log ((T + 1)²/δ))²`, so `ηA ≤ log (d (T + 1)²/δ)`, `e^{-ηA} ≥ δ/(4 d T²)` and the
threshold of L15 is `≥ 0.48 δ / (400 d² T⁴) ≥ δ / (1000 d² T⁴)`.

### 2.9 Lemmas of the paper that the blueprint does not use

- **Lemma 10** (exact balance) and **Lemma 11** (approximate vs exact): replaced by L33a, which
  compares directly with `η (ℓ j - ℓ i)`; no exact trajectory is needed. For the other areas
  (Theorem 6), the provable general form of Lemma 11 on `K ⊆ Δ` is
  `B̂^v(t₁, t₂) ≤ η ⟨L_[t₁,t₂), v⟩ + (t₂ - t₁) √(2^ν c₂ ε / ψ^ν)` for `‖v‖₁ = 1`, under
  `ŵ_t^k ≥ ψ` for `t₁ < t ≤ t₂`, `k ∈ supp v`, and `ε ≤ 2^{ν-2} c₂ ψ^{2-ν}` (same proof as L33a with
  `x = ŵ + uψv`: coordinates stay `≥ ψ/2` since `|v^k| ≤ 1/2`, `r'' ≤ 2^ν c₂/ψ^ν` there, and
  `‖v‖₂² ≤ 1/2`). Not checked numerically for `ν > 1`; it agrees with
  `notes/constants-barrier-polytope.md` (B7, B-6), which also gives the version without the side
  condition (extra `2ε/ψ` per round).
- **Lemma 12**: not used on the simplex.
- **Lemmas 37, 38**: only used by v2's proof of Lemma 39, replaced by L39 above.
- **Lemma 31** (`∑ v = 0`): only in the remark above.

## 3. Errata (area A)

Candidates for `notes/paper-errata.md` (numbers `E…` to be assigned there). Locations are in v2,
pages of the arXiv PDF.

- **A1. Theorem 5 is false for losses in `[-1, 1]^d`.** p. 6 (statement), p. 10 (proof, "Any
  adversarial sequence over the simplex is T/2-balanced"). For `[-1, 1]^d` the balance can be `T`
  (the `\opt{…}` block at line 1597 of `main.tex`, not typeset since `\optfalse`, says
  "`T`-balanced … with `α = T`"); the T/2 argument needs `[0, 1]^d`. Counterexample (§4 check 5):
  `d = 2`, `η = T^{-1/2}`, `ε` at the paper's threshold, losses `(1, -1)` for `0.35 T` rounds then
  `(-1, 1)`: regret `≈ 0.6 T` (`T = 10⁴, 4·10⁴`), while `log 2/η + ηT = O(√T)`. Correction (user
  decision): losses in `[0, 1]^d`, keeping `e^{-ηT/2}`. Kind: false statement.
- **A2. Initialisation missing in Lemma 15 and Theorem 5.** pp. 6, 10, 29. Lemmas 39, 40 use
  `w_1 = (1/d, …, 1/d)`. Counterexample without it (§4 check 6), even at the corrected threshold
  and with losses in `[0, 1]^2`: `ℓ_t = (0, 1)`, `w_1 = (e^{-0.6√T}, ·)`, `η = T^{-1/2}`: the
  constant trajectory is ε-approximate for `T ≥ 10⁵` and has regret `≈ T` vs
  `D_R(e_1, w_1)/η + ηT ≈ 0.6 T`. Correction: `a 0 = ū`. Kind: missing hypothesis.
- **A3. Comparator term.** Lemma 15, Theorem 5 (pp. 6, 10), Lemma 39 (p. 26, conclusion
  `Reg(w) ≤ D_R(w, ŵ_1)/η + …` "w.r.t any w"). The proofs bound only `Reg(w*)`, then
  `Reg(w) ≤ Reg(w*)`, which gives `D_R(w*, w_1)/η = log d/η`, not `D_R(w, w_1)/η`. Correction:
  `log d / η`. Whether the stronger form holds is open (§5). Kind: gap in the proof.
- **A4. Lemma 24, wrong constant.** p. 15, statement and last display of the proof (p. 16).
  `ε ≥ (h/2) x² - 2η x` gives, by Lemma 23 with `a = h/2`, `b = 2η`, `c = ε`,
  `x < 4η/h + √(2ε/h)`, not `√(ε/h)`. The statement is false (§4 check 2: `d = 2`, zero loss,
  `a_i = 0.01`, `ε = 10⁻⁶`, `η = 10⁻⁹`: step `1.404·10⁻⁴ >` bound `1.000·10⁻⁴`). Also: `h` must be
  the minimum of `r''` on the segment (the minimum at the endpoints only for monotone `r''`, fine for
  the entropy); `η ≤ 1/4` is unused; `‖w̃ - w_{t+1}‖ = 2(w_{t+1}^i - w_t^i)` should be `2|·|`.
  Correction: `|w_t^i - w_{t+1}^i| ≤ 4η/h + √(2ε/h)` (L24). Kind: wrong constant (false statement).
- **A5. Lemma 25, proof.** p. 17, eqs (6)–(8). The proof uses the wrong constant of Lemma 24; with
  `√(2ε/h)` it needs `ε ≤ x/32` (`ν = 1`, `c₁ = 1`). For the entropy the statement (`ε ≤ x/16`) is
  nevertheless true (§4 check 3: the exact thresholds are `0.098 x` forward, `0.135 x` backward).
  For general `c₁`, (6) has `4c₁ηw` and `√(c₁εw)` where `4ηw/c₁` and `√(2εw/c₁)` are meant (from
  `h ≥ c₁/w^ν ≥ c₁/w`), so the hypotheses should read `η ≤ c₁/16`, `ε ≤ c₁ x/32` (for area B to
  confirm). Correction used here: L25 (`ε ≤ x/32`). Kind: gap in the proof (wrong constant).
- **A6. Lemma 22, sign.** p. 15, second case of the proof: "`∇f(ŵ)(w - ŵ) ≥ ‖w - ŵ‖√(2βε)`"
  should be `≥ -‖w - ŵ‖√(2βε)`. Kind: typo.
- **A7. Lemma 11.** p. 8 (statement), p. 20 (proof). (a) On `[ŵ_t, ŵ_t + ψv]` with `‖v‖₁ = 1`,
  `∑ v = 0`, so `|v^k| ≤ 1/2`, coordinates go down to `ψ/2`, and the effective smoothness is only
  bounded by `c₂ (2/ψ)^ν`, not `c₂/ψ^ν`. (b) The proof derives `√(2c₂ε/ψ^ν)` per step and
  concludes `√(c₂ε/ψ^ν)` (the `√2` is dropped in the last display). (c) The step producing `ŵ_t`
  uses `ℓ_{t-1}`; the proof writes `ℓ_t`, and the balance over `[t₁, t₂]` involves
  `ℓ_{t₁}, …, ℓ_{t₂-1}` (same in Lemma 10). (d) The main-text statement assumes `w_t^i ≥ ψ` (exact
  trajectory), the appendix `ŵ_t^i ≥ ψ`. (e) Only `t₁ < t ≤ t₂` are needed. For `ν = 1` the
  statement's constant is asymptotically sharp and no counterexample was found (§4 check 11), so
  it may be true, but it is not proved; provable form in §2.9. Kind: gap in the proof.
- **A8. Lemma 33 is false.** p. 23. "Direct consequence of Lemma 11 for `v = e_{i*} - e_i`", but
  `‖e_{i*} - e_i‖₁ = 2`, so even granting Lemma 11 the error is `2(t₂ - t₁)√(ε/ψ)`. One-step
  counterexample (§4 check 4, `d = 3`, zero loss, `T = 1`): error/`√(ε/ψ)` `= 1.9995` with all
  hypotheses of Lemma 33. Correction: `(t₂ - t₁)√(8ε/ψ)` under `ε ≤ 2ψ` and `ŵ_t ≥ ψ` for
  `t₁ < t ≤ t₂` only (L33′), or the budget form L33. Kind: false statement (wrong constant).
- **A9. Lemma 10, off-by-one.** p. 8, proof p. 19–20: `B^v(t₁, t₂) = η ⟨ℓ_{t₁:t₂-1}, v⟩`, not
  `ℓ_{t₁:t₂}`; the displayed optimality condition lacks the factor `η`. Kind: typo.
- **A10. Definitions 16–17.** p. 14: `D_R(w_{t-1}, w)` should be `D_R(w ‖ w_t)` (index and order of
  the arguments, cf. Section 2). Kind: typo.
- **A11. Lemma 38.** p. 25. (a) Assumes `η ≤ 1/4` but applies Lemma 25, which needs `η ≤ 1/16`.
  (b) Uses the wrong constant of Lemma 24 (`5·2^ν` becomes `(4 + √2) 2^ν`). (c) Typo
  `r''(ŵ_t^{i*})` for `r''(ŵ_t^i)`. (d) Gives only an upper bound on `∇φ_t(ŵ_t)^i`, while Lemma 39
  needs a lower bound (A12 b). Kind: gap in the proof.
- **A12. Lemma 39, proof.** pp. 26–28, eqs (9)–(11). (a) p. 26: `w̃_t` sets the coordinates of
  `S_t` to `0`, so the segment `[ŵ_t, w̃_t]` reaches `0` and its effective smoothness is infinite,
  not `r''(ξ')`. (b) "`(ηℓ^{i*} + ∇R(ŵ_t)^{i*} - ∇R(ŵ_{t-1})^{i*})(w̃^{i*} - 1) = -O(2^ν η²)`"
  (p. 27) is used as an upper bound on this product, which needs a lower bound on the `i*`
  component of `∇φ_t`; Lemma 38 gives an upper bound. (c) Eq. (10), p. 28: the three-point terms
  `-D_r(ŵ_t^i, ŵ_{t-1}^i)` exist only for `t` with `i ∈ S_t`, but are replaced by the sum over all
  `t` (this decreases the right-hand side: wrong direction), and Lemma 27 needs all of them.
  (d) p. 27: the telescoping pairs `(s_j - 1, t_j)` where `(s_{j+1} - 1, t_j)` is meant. (e) p. 27:
  the argument `i ∈ S_2` drops the `4` of Lemma 24 (harmless) and is unnecessary (Lemma 37 gives
  `D_r(0, ŵ_{s_1-1}) ≤ D_r(0, ŵ_1)`). (f) `2√(2r''(ξ')ε) ≤ 2η²` needs `ε ≤ η⁴/(2r''(ξ'))`; the next
  display has `-η²` for `-2η²`. (g) `∑_{t=2}^T ⟨ℓ_{t-1}, ŵ_t - w*⟩` omits the round `T`. (h)
  Conclusion only for `w*` (A3). Correction: the new proof L39, with hypothesis `ε ≤ η⁴ ξ / 16` (no
  `ξ' = min{η/d, ξ}`) and conclusion `≤ log d/η + ηT`. Kind: gap in the proof.
- **A13. Lemma 40.** pp. 28–29. (a) Statement `T ≥ 4`, proof "since `T ≥ 3`". (b) With the
  corrected Lemmas 25 and 33, `ε ≤ 1/(r''(ξ/2) T²) = ξ/(2T²)` is not enough: the proof needs
  `ε ≤ ξ/32` (Lemma 25) and `ε ≤ ξ/(16 T²)` (balance `≤ k + 1`). Correction: `ε ≤ ξ/(32 T²)`, any
  `T ≥ 1` (L40). (c) "`≤ 1/(16 r''(ŵ_{t-1}^i))`" should be `ŵ_{t-1}^{i*}`. (d) "some `i ∈ [d]`"
  should be `i ≠ i*`. (e) The backward use of Lemma 25 (`ŵ_s^i ≥ ŵ_{s+1}^i/2`) is unnecessary
  with L33. Kind: wrong constant.
- **A14. Lemma 15.** p. 10, proof p. 29. (a) "`ε ≤ 1/(16de^{αη+1}T²) = 1/(r''(1/16de^{αη+1})T²)`":
  Lemma 40 needs `1/(r''(ξ/2)T²)`, i.e. `2` for `16` (and `16` is not implied by the hypothesis);
  typo. (b) With A13 the factor `6` of `max{6e^{ηα}, 1/η}` is insufficient: `32e ≈ 87` is needed,
  `100` is used. (c) The `1/η` branch (from `ξ' = min{η/d, ξ}` in Lemma 39) is unnecessary with
  L39. (d) A2. (e) A3. (f) `O(Tη)` is `Tη`. (g) `T ≥ 3` is unnecessary. Kind: wrong constant
  (and missing hypothesis, A2).
- **A15. Theorem 5, reduction to Lemma 15.** p. 6, proof p. 10. The threshold of Theorem 5 drops
  the `1/η` branch, so it does not imply the threshold of Lemma 15 (as stated) with `α = T/2`:
  `η = 1/16`, `T = 3`: `1.16·10⁻⁶/d` vs `4.77·10⁻⁷/d` (§4 check 8). With the corrected Lemma 15
  the branch is not needed; the constant `6` becomes `100`; `T ≥ 3` is unnecessary. Kind: gap in the
  proof (wrong constant).
- **A16. Theorem 7.** p. 7, proof p. 10. (a) `T ≥ 256` does not give `η = √(log d/T) ≤ 1/16`
  (needed by Lemma 15) once `d ≥ 3` (`d = 3`, `T = 256`: `η = 0.0655`); correction
  `T ≥ 256 log d`. (b) `α` is the balance w.r.t. the empirical best arm `i*`, which is random:
  Hoeffding for a fixed pair does not apply; the sum `L^{i*}_{[s,t)} - L^i_{[s,t)}` has a drift
  `(t - s)(μ^{i*} - μ^i)` that must be controlled through the optimality of `i*` (L7a uses the
  bridge `Z`). (c) "`ηα ≤ log(dT²/δ)`": the constant of the Hoeffding/union bound is not `≤ 1`;
  even the sharp bound `ηα ≤ √(2 log d log(N/δ))` of L7a (`N` the number of events of the union
  bound, `≥ d²T²/2`) exceeds `log(dT²/δ)` when `log d` is large compared with `log(T²/δ)` (e.g.
  `log d = 20`, `T = 256 log d`, `δ = 1/2`, `N = d²T²`: `48.1 > 37.8`, §4 check 8); it holds when
  `T ≥ d`. (This shows that the proof's claim fails, not that the true balance does.) Correction:
  `e^{ηα} ≤ d²(T+1)/√δ` (L7b), which leads to `ε ≤ δ/(6d³T⁴)`. (d) For `d = 2`,
  `min{η⁴, T⁻²} = (log 2)²/T²`, so even granting (c) the threshold `δ/(6d²T⁴)` overstates what
  Lemma 15 gives by `1/(log 2)² ≈ 2.08`. (e) `d = 1` gives `η = 0` (trivial case). (f)
  `O(√(T log d))` is `2√(T log d)`. Kind: missing hypothesis (a), gap in the proof (b, c), wrong
  constant (c, d).
- **A17. Lemma 13, proof.** p. 22: "Since `w_{t₂}^i ≥ w_{t₂}^i`" should be `w_{t₂}^i ≥ w_{t₁}^i`;
  the contradiction hypothesis `e^k w_{t₂}^{i*} < w_{t₁}^{i*}` should have `e^{k/c₁}`. Kind: typo.
- **A18. Balance of the simplex, sign.** p. 10, before "Implications": "if for every `i`,
  `ℓ^i_{t₁:t₂} - ℓ^{i*}_{t₁:t₂} ≤ α`, it follows that the loss sequence is α-balanced". A one-sided
  bound does not give the two-sided Section 5.1 notion (`⟨ℓ, v⟩ ≤ α‖v‖` for all `v ∈ ker A`), and
  the proofs (Lemmas 13, 40, Definition 32) use the other sign, `ℓ^{i*} - ℓ^i ≤ α`. Lemma 15 is
  stated (modelling.md) with the one-sided notion `L^{i*} - L^i ≤ α`. Kind: typo.

## 4. Numerical checks

Scripts and outputs (`sNN_*.py`, `sNN_output.txt`) in
`/tmp/claude-663481/-home-rdegenne-Documents-Lean-Schlisselberg2026Hidden/7ad2edfa-b559-4fea-932a-1aff1e8cf05b/scratchpad/entropy-upper/`,
run with `python3 -I` (mpmath at 40–300 digits where coordinates reach `e^{-ηT}`; numpy/scipy for
Monte Carlo and optimisation). The ε-steps are generated through the characterisation of L26′
(points of `Δ` at relative entropy `≤ ε` from the exact Hedge update), checked in check 1.

1. `s01_identities.py`: 3000 random high-precision instances (`d ≤ 6`, ε down to `10⁻²⁵`,
   coordinates down to `e^{-30}`, ε-steps on the boundary of the relative-entropy ball): the
   objective identity L26′ and the characterisation (error `≤ 3·10⁻⁵⁹`), L21a, L21b, the vertex
   bound of L39 step 1, Pinsker, and the per-step inequalities of L39 (steps 1–2) and L33a:
   no violation.
2. `s02_lemma24.py`: three explicit counterexamples to v2's Lemma 24 (e.g. `a_i = 0.01`,
   `ε = 10⁻⁶`: step `1.4039·10⁻⁴`, bound `1.0000·10⁻⁴`); the corrected L24 over a grid of `a_i`
   (down to `2⁻²⁹`), `η ≤ 1/16`, `ε`, and extreme losses: max of step/bound `= 0.9988` (tight).
3. `s03_lemma25.py`: exact worst case of Lemma 25 for the entropy, `η = 1/16`: the step ratio
   `1/2` needs relative entropy `≥ 0.0984 x` (forward) and `≥ 0.1347 y` (backward), so v2's
   `ε ≤ x/16` statement holds and L25's `x/32` has margin.
4. `s04_lemma33.py`: one-step counterexamples to v2's Lemma 33 (ratio error/`√(ε/ψ)` =
   `1.9995`, `1.99975`, `1.99995`, all hypotheses satisfied); numerical sup of the ratio over
   ε-steps with `â^i, â^{i*} ≥ ψ`, `ε ≤ 2ψ`: `2.17` (bound of L33′: `√8 = 2.83`).
5. `s05_thm5_pm1.py`: A1. `[-1, 1]` losses, paper's threshold: `T = 10⁴`: regret `6069.8`
   (`0.607 T`), `log 2/η + ηT = 169.3`; `T = 4·10⁴`: `24139` (`0.6035 T`) vs `338.6` (ratio grows
   like `√T`). Same construction with `[0, 1]` losses and the corrected threshold: not stuck, regret
   `35.4, 70.1, 139.4` (`T = 2500, 10⁴, 4·10⁴`) below `84.7, 169.3, 338.6`.
6. `s06_thm5_init.py`: A2. Stuck constant trajectory from `w_1 = (e^{-0.6√T}, ·)` allowed for
   `T = 10⁵, 10⁶, 10⁸` at the corrected threshold; regret / (`D(e_1, w_1)/η + ηT`) `→ 1.666`.
7. `s07_balance01.py`: L5a exhaustively on grids (`d = 2`, `T ≤ 6`, values `{0, ½, 1}`; `d = 3`,
   `T ≤ 4`, `{0, 1}`) and 3000 random real sequences: `≤ min(t - s, T - (t - s))` always, `T/2`
   attained for even `T`; `[-1, 1]` two-phase sequences reach `T`.
8. `s08_thresholds.py`: A15 example (`η = 1/16`, `T = 3`, also `T = 10`, `η = 0.01`); `32e = 86.99`,
   `16e = 43.49`; grid check that the L15 threshold implies `ε ≤ ξ/(32T²)` and `ε ≤ η⁴ξ/16`;
   `η(T = 256) > 1/16` for `d ≥ 3`; AM–GM of L7b.2; L7b.4 on a grid (`d` up to `10⁸`, `T` from
   `256 log d` to `10⁹`, `δ` down to `10⁻⁵⁰`): the L15 threshold is `≥ 64 ×` `δ/(6d³T⁴)` and
   `≥ 11 ×` `√δ/(500 d³T³)`; failure of "`ηα ≤ log(dT²/δ)`" for `log d ≥ 20` (A16 c) and its
   validity on a grid with `T ≥ d` (7c).
9. `s09_simulate.py`: greedy adversary (each step minimises `a^{i*}` within the relative-entropy
   ball) on two-phase `[0, 1]` losses (`d = 2, 3`, `α = 78`), uniform `[0, 1]` and Rademacher losses
   (`d = 4`), `T = 160`, `η = 1/16`: at the L15 threshold `min a^{i*}/ξ ≥ 3.7` and
   regret/(`log d/η + ηT`) `≤ 0.48`; at `10⁴ ×` the threshold the adversary already drives `a^{i*}`
   to `10⁻⁵⁰` (sanity check that the thresholds are not vacuous; not a tightness claim).
10. `s10_bridge_mc.py` (Monte Carlo, 4000 runs each, Rademacher / Bernoulli with close means /
    uniform `[0,1]` / correlated losses, `d ∈ {2, 5, 20}`, `δ = 0.1`): `P(balance > A) = 0` in all
    cases (L7a is conservative); `η ×` the `(1 - δ)`-quantile of the balance is `0.4–3.7`.
11. `s11_lemma11_nu1.py`: numerical sup (Nelder–Mead, 300 starts, `ψ ∈ [10⁻⁵, 0.2]`,
    `ε ≤ ψ/2`, both iterates `≥ ψ`) of the one-step error of Lemma 11 (`ν = 1`,
    `v = (e_{i*} - e_i)/2`) over `√(ε/ψ)`: `0.99982`. No counterexample to the statement of
    Lemma 11 for `ν = 1`; `1` is the asymptotic sup, so the statement is sharp but unproved (A7).

## 5. Open points and doubts

1. **Comparator term (A3).** Is `Regret(u) ≤ D(u, ū)/η + C ηT` true for every `u ∈ Δ` under the
   thresholds above? Plausible (the regret is linear in `u` and the bad arms have very negative
   regret), but neither v2 nor this blueprint proves it. The corrected statements use `log d/η`.
2. **Constants not optimised.** The `100` of Lemma 15 / Theorem 5 is forced by the proof
   (`≥ 32e ≈ 87`); v2's `6` may still be true (the analysis loses constant factors in L21a, L33a,
   L25), but it is unproved. Theorem 7 with `d²` (v2) instead of `d³` is unproved without an extra
   hypothesis such as `T ≥ d` (variant 7c).
3. **Choice between variants of Theorem 7** (`T ≥ 256 log d` with `C = 2`, or no `T` hypothesis
   with `C = 32`; `δ/(6d³T⁴)` or `√δ/(500d³T³)`): for the user.
4. **Positivity of `a T`.** (T2) includes the last iterate `a T`, which the regret does not use but
   L39 and L40 do (`g (T - 1)` involves `log (a T)`). An ε-step can have zero coordinates, so this
   is a genuine hypothesis; removing it would need L26′ without the gradient at `a (t + 1)`.
5. **Losses bounded surely** in Theorem 7 (`∀ t ω k`); an a.s. bound works by intersecting `E` with
   the a.s. event.
6. **General ν.** The remarks on Lemmas 11, 24 and 25 for `ν > 1` or `c₁ ≠ 1` (§2.9, A4, A5, A7)
   agree with `notes/constants-barrier-polytope.md` (B-2, B-3', B-6); A4–A8 should be merged with
   those entries when they go to `paper-errata.md`.
