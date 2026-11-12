# Theorem 6 (ν-barriers, ν > 1, on a polytope): corrected statement, blueprint, errata

Area B of the constants pass on [SSKM26] (arXiv:2511.22283v2, `source/arXiv-2511.22283v2/main.tex`):
Theorem 6 (`thm:ub_nonentropy`, Section 4.1), its sketch (Section 5.2) and its proof (appendix
"Proof of Theorem 6": Lemmas 41, 42 and the final computation), with the lemmas it uses
(10, 11, 12, 21–27, 29–31). Lemma numbers are those of v2 (one shared counter). The conventions
are those of `notes/modelling.md`: Lean rounds start at `0`, `a 0` is the paper's `w_1`, the regret
of `T` rounds uses `a 0, …, a (T-1)`, and a trajectory of `T` rounds also has `a T`.

**Verdict.** The polytope case can be repaired, and the statement below is true with fully
explicit constants. The paper's proof has two gaps and several wrong constants:
- Lemma 25 is used on a polytope but is proved only on the simplex.
- Lemma 22 is applied on a segment where the smoothness bound fails.
- Lemma 41 lacks a factor `1/(ν-1)`. This makes Lemma 42 false for `ν > 9`, already for exact
  OMD on the 2-simplex.
- The threshold of the theorem does not imply the one used in Lemma 42 when `ν > 2`.
- The `O(ηT)` term must depend on `c₁`.

The repair replaces Lemma 25 with a "pull toward the initial point" argument (Lemma 25-P below).
That argument needs no exact minimizer, no smoothness and no condition on `η`.

---------------------------------------------------------------------------------------------------

## 1. Corrected statement

### 1.1 Setting (Lean shape)

- `α` is a finite type and `d = Fintype.card α`. The case `d = 1` is trivial (see B0).
- `K = {w | (∀ i, 0 ≤ w i) ∧ A w = b}` for a linear map `A` from `α → ℝ` to a real vector space,
  with `K ⊆ simplex α`. Write `K⁺ = {w ∈ K | ∀ i, 0 < w i}`.
- The barrier is given by `r : ℝ → ℝ`, `ν : ℝ` with `1 < ν`, and `0 < c₁`, `0 < c₂`. On `Set.Ioo 0 1`,
  `r` is differentiable, `r' := deriv r` is differentiable, and `r'' := deriv (deriv r)` satisfies
  `c₁ / x ^ ν ≤ r'' x ≤ c₂ / x ^ ν` (real powers). We do not assume `r''` monotone, and nothing
  is assumed about `r 0`. Then `R w = ∑ i, r (w i)` and `∇R(w) = (r' (w i))_i`.
- The Bregman divergence is `D_R(y, x) = R y - R x - ∑ i, r' (x i) * (y i - x i)`
  (LML `bregDiv R y x (∇R x)`). The step objective of round `t` is
  `Φ_t(w) = η ⟨ℓ t, w⟩ + D_R(w, a t)`, with `⟨ℓ, w⟩ = ∑ i, ℓ i * w i`.
- Learning rate `0 < η`, error `0 ≤ ε`, horizon `T : ℕ`. Losses satisfy `ℓ t i ∈ [-1, 1]` for
  `t < T`.
- The trajectory `a : ℕ → α → ℝ` satisfies:
  - `a 0 = p := fun _ ↦ 1 / d`, and `p ∈ K`;
  - `a t ∈ K⁺` for every `t ≤ T`;
  - for every `t < T`, `a (t + 1)` is an ε-approximate mirror descent step on `K` from `a t` for
    the loss `ℓ t`: `Φ_t(a (t+1)) ≤ Φ_t(b) + ε` for every `b ∈ K`.

  The proof only uses comparison points `b ∈ K⁺`. So the theorem also holds with the step defined
  by "for every `b ∈ K⁺`", which is the faithful reading for barriers: in Lean, `Φ_t(b)` for a
  boundary `b` uses the junk value `r 0`.
- The constants:
  ```
  Ψ := (2d)^(ν-1) + 8 (ν-1) η T d / c₁,      ψ := Ψ ^ (-1/(ν-1))    (so ψ^(1-ν) = Ψ, 0 < ψ ≤ 1/(2d))
  threshold:  ε ≤ η⁴ ψ^ν / (4^(ν+2) · max 1 c₂)
           =  η⁴ ((2d)^(ν-1) + 8(ν-1)ηTd/c₁)^(-ν/(ν-1)) / (4^(ν+2) · max 1 c₂).
  ```

### 1.2 Theorem 6 (corrected): headline

Assume the setting of 1.1 and the threshold. Then, for every comparator `u ∈ K` with
`∀ i, 0 < u i`:

```
∑ t < T, (⟨ℓ t, a t⟩ - ⟨ℓ t, u⟩)  ≤  D_R(u, p) / η + (1 + 1/c₁) η T.
```

The constant `1 + 1/c₁` depends only on `c₁`. The threshold depends on `ν`, `c₁` (through `ψ`)
and `c₂`. There is no hypothesis on `η` beyond `0 < η`: the paper's `η ≤ 1/(16 c₁)` is dropped.

### 1.3 Comparators with zero coordinates (choice (c))

**Theorem 6' (extension).** Assume in addition `ContinuousWithinAt r (Set.Ici 0) 0`. Then the
bound of 1.2 holds for every `u ∈ K`.

**Core form (no hypothesis on `r 0`).** If `0 < η ≤ 2`, then for every `u ∈ K`,
`Regret(u) ≤ (D_R(u, p) - D_R(u, a T)) / η + (1 + 1/c₁) η T`.
In this form `R u` cancels, so it does not matter what `r 0` is.

**Why (c).**
- A bound "for all `u ∈ K`" with no hypothesis is false in Lean. For the log barrier,
  `-log 0 = 0` makes `D_R(e₁, p) = -d log d < 0`. Concretely, take `d = 2`, `T = 1`, `η = 0.1`,
  `ℓ 0 = (-1, 1)` and `u = e₁`: the regret is `⟨ℓ 0, p - e₁⟩ = 1`, while the right-hand side is
  `-2 log 2 / 0.1 + (1 + 1)·0.1 ≈ -13.66`.
- Option (a) alone (right-continuity) would exclude the log barrier (`ν = 2`), one of the
  paper's three examples. For the log barrier and a boundary `u`, the paper's right-hand side is
  `+∞`, so restricting to positive `u` loses nothing there.
- Option (b) alone would lose Tsallis entropies (`1 < ν < 2`) at vertices, where the paper's bound
  is finite and the best fixed point usually lies. In Lean, `(x - x^q)/(1-q)` with `Real.rpow` is
  right-continuous at `0`, so Theorem 6' covers them.
- The negative entropy (`ν = 1`) is not in the scope of Theorem 6.

Proof of Theorem 6' from the core form: right-continuity together with convexity of `r` on
`(0, 1)` gives `D_r(0, x) ≥ 0`, hence `D_R(u, y) ≥ 0` for `u ∈ K` and `y ∈ K⁺` (B15).

### 1.4 Lemma 42 (corrected): iterate lower bound

Under the setting of 1.1 and the two conditions

```
(E1) ε ≤ η² ψ^ν / (4^(ν+1) c₂)        (E2) ε ≤ η ψ / 8
```

(no condition on `η`), every iterate satisfies `ψ ≤ a t i` for all `t ≤ T` and all `i`. For
`0 < η ≤ 2`, the threshold of 1.1 implies (E1) and (E2).

### 1.5 Generalization: arbitrary initial point (the paper's footnote)

The proof never uses that `a 0` is uniform or that `p ∈ K`. It only uses `a 0 =: q ∈ K⁺` and
`m := min_i q i > 0` (`m ≤ 1/d`). With `1/d` replaced by `m` everywhere:

```
Ψ_q := (2/m)^(ν-1) + 8 (ν-1) η T / (c₁ m),   ψ_q := Ψ_q^(-1/(ν-1)),
ε ≤ η⁴ ψ_q^ν / (4^(ν+2) · max 1 c₂)   ⟹   Regret(u) ≤ D_R(u, q)/η + (1 + 1/c₁) η T.
```

Setting `q = p` (`m = 1/d`) gives 1.2. **Recommendation:** formalize this form, and the core form
of 1.3, and derive 1.2 and 1.3 as corollaries. The blueprint below is written for general `q`.

### 1.6 Deviations from the paper (each is an erratum item of Section 3)

| item | paper (v2) | corrected | erratum |
|---|---|---|---|
| `ψ` | `(c₁/(8ηTd + c₁(2d)^(ν-1)))^(1/(ν-1))` | `((2d)^(ν-1) + 8(ν-1)ηTd/c₁)^(-1/(ν-1))` | B-3, B-4 |
| threshold | `η⁴ min{1/c₂, c₂} (16ηTd/c₁ + 2(2d)^(ν-1))^(-ν/(ν-1))` | `η⁴ ψ^ν / (4^(ν+2) max{1, c₂})` | B-4, B-5, B-6, B-7 |
| hypothesis on `η` | `η ≤ 1/(16c₁)` | none (`0 < η`) | B-8 |
| `O(ηT)` | unspecified | `(1 + 1/c₁) η T` (necessarily depends on `c₁`) | B-9 |
| comparators | all `w ∈ K` | `u ∈ K⁺`; all of `K` under right-continuity at `0` | B-10 |

Neither threshold implies the other. Ours is larger by a factor of about `10¹²` for `ν = 1.1`,
because the paper's `ψ` degenerates super-exponentially as `ν → 1` while ours tends to
`e^{-8ηTd/c₁}/(2d)`. It is smaller by `1/64` at `ν = 2`, and smaller by a factor of about `4^{-ν}`
for large `ν` (check C5). The factor `4^ν` comes from two halvings: the new iterate is first only
known to be `≥ ψ/2`, and the segments of Lemma 11' go down to `ψ/4`. Finer step sizes would reduce
it to a polynomial in `ν`. That refinement is not worked out here.

---------------------------------------------------------------------------------------------------

## 2. Blueprint

**Notation.**
- `D_r(y, x) = r y - r x - r' x * (y - x)`, so `D_R(y, x) = ∑ i, D_r(y i, x i)`.
- `‖v‖₁ = ∑ i, |v i|`.
- `G_t(w) := η ℓ t + ∇R(w) - ∇R(a t)` (the formal gradient of `Φ_t`).
- `S_q(y) := ⟨∇R(q) - ∇R(y), q - y⟩ = ∑ i, (r'(q i) - r'(y i)) (q i - y i)`.
- `δ := √(4^ν c₂ ε / ψ^ν) + 4 ε / ψ` (the per-round balance error of Lemma 11' at `ψ' = ψ/2`).
- `ψ`, `Ψ` and `m` are those of 1.5 (with `q = p`: `m = 1/d`).

Facts about the constants:
- `m ≤ 1/d ≤ 1/2`, since the minimum is at most the mean.
- `Ψ ≥ (2/m)^(ν-1)`, so `ψ ≤ m/2 ≤ 1/4`, `ψ^(ν-1) ≤ 1` and `ψ^ν ≤ 1`.
- `c₁ ≤ c₂` (not needed).

**B0. Trivial cases.**
- `d = 1`: `K = {q}` and every iterate is `q`, so the regret is `0 = D_R(q, q)/η` and the bound
  holds.
- `η > 2` (headline only): `|⟨ℓ t, a t - u⟩| ≤ ‖a t - u‖₁ ≤ ∑ a t i + ∑ u i = 2`, so
  `Regret(u) ≤ 2T < ηT`. Moreover `D_R(u, q) ≥ 0` for `u ∈ K⁺` by B4(c), and `1 + 1/c₁ ≥ 1`.
- From now on `d ≥ 2`, and in the regret part `0 < η ≤ 2`.

**B1. Constants lemma.** If `0 < η ≤ 2` and `ε ≤ η⁴ψ^ν/(4^(ν+2) max 1 c₂)`, then (E1), (E2)
and the following hold:

```
(E3) ε ≤ η⁴ ψ^ν / (2^(ν+4) c₂)        (E4) ε ≤ η²/8.
```

*Proof.* Let `θ := η⁴ψ^ν/(4^(ν+2) max 1 c₂)`.
- (E1): `θ ≤ η⁴ψ^ν/(4^(ν+2) c₂) = (η²/4) · η²ψ^ν/(4^(ν+1) c₂) ≤ η²ψ^ν/(4^(ν+1) c₂)`, since
  `η² ≤ 4`.
- (E2): `θ ≤ η⁴ψ^ν/4^(ν+2) = ηψ · η³ψ^(ν-1)/4^(ν+2) ≤ ηψ · 8/64`, since `η³ ≤ 8`,
  `ψ^(ν-1) ≤ 1` and `4^(ν+2) ≥ 4³` (as `ν ≥ 1`).
- (E3): `4^(ν+2) = 2^(2ν+4) ≥ 2^(ν+4)` and `max 1 c₂ ≥ c₂`.
- (E4): `θ ≤ η² · η²ψ^ν/4^(ν+2) ≤ η² · 4/64`. ∎

Consequence: `δ ≤ η`. By (E1), `4^ν c₂ ε/ψ^ν ≤ η²/4`, so the square root is `≤ η/2`. By (E2),
`4ε/ψ ≤ η/2`. Also `ε ≤ ηψ` by (E2).

**B2. Polytope facts (replaces Lemma 31).** Let `d ≥ 2`.
- (a) If `w ∈ K⁺`, then `w i < 1` for every `i`, since `w i = 1 - ∑_{j≠i} w j` and `d ≥ 2`.
- (b) If `x, y, z ∈ K`, `γ ∈ ℝ` and `x + γ(y - z) ≥ 0` coordinatewise, then `x + γ(y - z) ∈ K`,
  because `A(x + γ(y - z)) = b + γ(b - b)`.
- (c) `K` is convex.
- (d) For `y, z ∈ K`, `∑ i, (y i - z i) = 0`, since `K ⊆ simplex`. If `∑ v = 0`, then
  `|v i| ≤ ‖v‖₁/2` (as `|v i| = |∑_{j≠i} v j| ≤ ‖v‖₁ - |v i|`), and therefore
  `∑ (v i)² ≤ (max |v i|) ‖v‖₁ ≤ ‖v‖₁²/2`.

Lemma 31 (`∑ v = 0` for `v ∈ ker A`) is not needed. Only differences of points of `K` occur.

**B3. Lemma 41' (corrected).**
- `r'` is monotone on `(0, 1)`, since `r'' > 0`.
- For `0 < x ≤ y < 1`: `r' y - r' x ≥ (c₁/(ν-1)) (x^(1-ν) - y^(1-ν))`.

*Proof.* `f(s) = r'(s) + c₁ s^(1-ν)/(ν-1)` has `f'(s) = r''(s) - c₁ s^(-ν) ≥ 0` on `(0, 1)`, so
`f` is monotone there. ∎

The factor `1/(ν-1)` is the correction of Lemma 41 (erratum B-3).

**B4. Lemma 21' (one-dimensional Taylor bounds).** Let `x, y ∈ (0, 1)` and let `I` be the closed
interval between them.
- (a) If `r'' ≤ M` on `I`, then `D_r(y, x) ≤ M (y - x)²/2`.
- (b) If `r'' ≥ μ` on `I`, then `D_r(y, x) ≥ μ (y - x)²/2`.
- (c) `D_r(y, x) ≥ 0`.
- (d) `D_r(y, x) ≥ c₁ (y - x)² / (2 max(x, y))`.

*Proof.*
- (a), (b): `g(s) = r s - r x - r' x (s - x) - M (s - x)²/2` has `g x = 0`, `g' x = 0` and
  `g'' = r'' - M ≤ 0` on `I`. So `g'` is antitone, with `g' ≤ 0` to the right of `x` and `g' ≥ 0`
  to the left, hence `g ≤ 0` on `I`. Symmetrically for (b).
- (c): (b) with `μ = 0`.
- (d): (b) with `μ = c₁/max(x, y)`. For `s ∈ I`, `s ≤ max(x, y) < 1` and `s^ν ≤ s` (as
  `s ∈ (0, 1)` and `ν ≥ 1`), so `r'' s ≥ c₁/s^ν ≥ c₁/s ≥ c₁/max(x, y)`. ∎

This replaces Lemma 21 / Definition 20 ("effective smoothness"), which is stated for a whole
segment. Every use below takes `M` from the explicit range of the coordinates on the segment.

**B5. Lemma 26 and the Bregman identity of `Φ_t`.** Pure algebra, valid for any values of
`R u` (junk included):
- (a) **Three points:** `⟨∇R(x) - ∇R(a), u - x⟩ = D_R(u, a) - D_R(u, x) - D_R(x, a)`. Here `R u`
  cancels.
- (b) `Φ_t(y) - Φ_t(z) - ⟨G_t(z), y - z⟩ = D_R(y, z)`, since the rest of `Φ_t` is affine.
  Consequently, for `y, z ∈ K⁺` (by B2(a) and B4(c)): `Φ_t(z) - Φ_t(y) ≤ ⟨G_t(z), z - y⟩`.
- (c) `Φ_t(x + γh) - Φ_t(x) = γ⟨G_t(x), h⟩ + [R(x + γh) - R(x) - γ⟨∇R(x), h⟩]`.

**B6. Lemma 22' (localized approximate first-order condition).** Let `t < T`, `x = a (t+1)`,
`h : α → ℝ`, `γ₀ > 0` and `Q ≥ 0`. Assume that for every `γ ∈ (0, γ₀]`, `x + γh ∈ K⁺` and
`R(x + γh) - R(x) - γ⟨∇R(x), h⟩ ≤ γ² Q / 2`. Then

```
⟨G_t(x), h⟩ ≥ -(√(2εQ) + 2ε/γ₀).
```

*Proof.* By the ε-step with `b = x + γh` and B5(c), `-ε ≤ γ⟨G_t(x), h⟩ + γ²Q/2`. So
`g := ⟨G_t(x), h⟩ ≥ -ε/γ - γQ/2` for every `γ ∈ (0, γ₀]`.
- If `ε = 0`, letting `γ → 0` gives `g ≥ 0`.
- If `ε > 0`, `Q > 0` and `γ₁ := √(2ε/Q) ≤ γ₀`, take `γ = γ₁`: `ε/γ₁ + γ₁Q/2 = √(2εQ)`.
- Otherwise `Q γ₀² < 2ε`. Take `γ = γ₀`: `ε/γ₀ + γ₀Q/2 < 2ε/γ₀`. ∎

This corrects Lemma 22: only the initial part `[x, x + γ₀h]` of the segment needs a smoothness
bound (errata B-6, B-12).

**B7. Lemma 11' (one-step balance, corrected).** Let `t < T` and `0 < ψ' < 1` with
`a (t+1) i ≥ ψ'` for all `i`. Then for all `y, z ∈ K`:

```
⟨∇R(a t) - ∇R(a (t+1)), y - z⟩ ≤ η ⟨ℓ t, y - z⟩ + (√(c₂ (2/ψ')^ν ε) + 2ε/ψ') ‖y - z‖₁.
```

*Proof.*
1. The left side minus `η⟨ℓ t, y - z⟩` equals `-⟨G_t(x), y - z⟩`, with `x = a (t+1)`.
   Let `v = y - z`. The case `v = 0` is trivial. Otherwise put `h = v/‖v‖₁`. By B2(d),
   `|h i| ≤ 1/2` and `∑ (h i)² ≤ 1/2`.
2. Take `γ₀ = ψ'`. For `0 ≤ s ≤ γ ≤ ψ'`, the coordinates of `x + sh` are `≥ ψ' - ψ'/2 = ψ'/2`.
   By B2(b), `x + sh ∈ K⁺`, and by B2(a) its coordinates lie in `[ψ'/2, 1)`.
3. So `r'' ≤ c₂/(ψ'/2)^ν =: M` on every interval between `x i` and `x i + γ h i`. By B4(a),
   `R(x + γh) - R(x) - γ⟨∇R(x), h⟩ = ∑ D_r(x i + γ h i, x i) ≤ (M γ²/2) ∑ (h i)² ≤ γ² (M/2)/2`.
4. B6 with `Q = M/2` gives `⟨G_t(x), h⟩ ≥ -(√(εM) + 2ε/ψ')`. Multiply by `‖v‖₁`. ∎

We use it with `ψ' = ψ/2`, where the error term is exactly `δ`.

**B8. Lemma 10' (balance accumulation, corrected indices).** Let `t ≤ T`, and assume
`a (s+1) ≥ ψ/2` coordinatewise for every `s < t`. Then for all `y, z ∈ K`:

```
⟨∇R(q) - ∇R(a t), y - z⟩ ≤ t (η + δ) ‖y - z‖₁.
```

*Proof.* Telescoping with `a 0 = q`:
`⟨∇R(q) - ∇R(a t), v⟩ = ∑_{s<t} ⟨∇R(a s) - ∇R(a (s+1)), v⟩`.
By B7 with `ψ' = ψ/2`, each term is `≤ η⟨ℓ s, v⟩ + δ‖v‖₁`, and `η⟨ℓ s, v⟩ ≤ η‖v‖₁` since
`|ℓ s i| ≤ 1`. ∎

For exact steps (`ε = 0`) this is Lemma 10 with `ℓ_{t₁:t₂-1}` (erratum B-11), as an inequality.

**B9. Lemma 12' (balance to coordinate lower bound, corrected).** Let `κ ≥ 0` and
`ψ_κ := ((2/m)^(ν-1) + 2(ν-1)κ/(c₁ m))^(-1/(ν-1))`. If `y ∈ K⁺` and `S_q(y) ≤ κ`, then
`y i ≥ ψ_κ` for every `i`. With `κ = 4ηT`, `ψ_κ = ψ`.

*Proof.*
1. Every term `(r'(q i) - r'(y i))(q i - y i)` of `S_q(y)` is `≥ 0`, because `r'` is monotone
   (B3) and `q i, y i ∈ (0, 1)` (B2(a)). So `S_q(y)` dominates each term.
2. Suppose `y i < ψ_κ`. Since `ψ_κ ≤ m/2 ≤ q i / 2`, we have `y i < q i`, and
   `q i - y i > q i - m/2 ≥ m/2 > 0`.
3. By B3: `r'(q i) - r'(y i) ≥ (c₁/(ν-1)) ((y i)^(1-ν) - (q i)^(1-ν))`.
4. Now `(y i)^(1-ν) > ψ_κ^(1-ν)`, and `(q i)^(1-ν) ≤ (m/2)^(1-ν) = (2/m)^(ν-1)`, because
   `t ↦ t^(1-ν)` is antitone. So the right side of step 3 is
   `> (c₁/(ν-1)) (ψ_κ^(1-ν) - (2/m)^(ν-1)) = 2κ/m ≥ 0`.
5. Multiplying (`a > A ≥ 0` and `b > B > 0` give `ab > AB`), the `i`-th term is
   `> (2κ/m)(m/2) = κ ≥ S_q(y)`. This contradicts step 1. ∎

Compared with Lemma 12 (appendix restatement), which is correct:
`−r'(w_t^i) ≤ max{4kd − r'(1/d), −r'(1/2d)}`. The main-text form follows from it. Using the
termwise form avoids the minimizing coordinate `ī` and the case split on `v^ī` (erratum B-13).

**B10. Lemma 25-P (replaces Lemma 25 on polytopes).** Let `t < T`. Assume (E1), (E2), and
`a (s+1) ≥ ψ/2` coordinatewise for every `s < t`. Then `a (t+1) i ≥ ψ/2` for every `i`.

*Proof.* Let `x = a (t+1) ∈ K⁺` and `λ := ψ/2 ∈ (0, 1/8]`. Let `z := (1-λ) x + λ q`. Then
`z ∈ K` by B2(c), and `z i ≥ λ q i > 0`, so `z ∈ K⁺`. Note `z - x = λ(q - x)` and
`q - x = (q - z)/(1-λ)`.
1. The ε-step with `b = z` gives `Φ_t(x) ≤ Φ_t(z) + ε`. B5(b) gives
   `Φ_t(z) - Φ_t(x) ≤ ⟨G_t(z), z - x⟩ = λ⟨G_t(z), q - x⟩`. Hence `⟨G_t(z), q - x⟩ ≥ -ε/λ`.
2. Split `G_t(z) = η ℓ t + (∇R(z) - ∇R(q)) + (∇R(q) - ∇R(a t))`:
   - `⟨∇R(z) - ∇R(q), q - x⟩ = ⟨∇R(z) - ∇R(q), q - z⟩/(1-λ) = -S_q(z)/(1-λ)`;
   - `⟨∇R(q) - ∇R(a t), q - x⟩ ≤ t(η + δ)‖q - x‖₁ ≤ 2ηt‖q - x‖₁`, by B8 (hypothesis) and
     `δ ≤ η` (B1);
   - `η⟨ℓ t, q - x⟩ ≤ η‖q - x‖₁`.
3. With `‖q - x‖₁ ≤ 2`, `t ≤ T - 1` and `ε/λ = 2ε/ψ ≤ 2η` (by (E2)):
   `S_q(z)/(1-λ) ≤ ε/λ + (η + 2ηt)‖q - x‖₁ ≤ 2η + 2η(2T - 1) = 4ηT`.
   Hence `S_q(z) ≤ 4ηT`, since `0 < 1-λ ≤ 1` and the bound is `≥ 0`.
4. B9 with `κ = 4ηT` gives `z i ≥ ψ` for every `i`.
5. Finally `x i = (z i - λ q i)/(1-λ) ≥ z i - λ q i ≥ ψ - ψ/2 = ψ/2`, using `q i ≤ 1`,
   `z i - λ q i ≥ 0` and `1/(1-λ) ≥ 1`. ∎

Why this is the right repair.
- Lemma 25 (and Lemma 24) compare `w_{t+1}` with a point `w̃` that moves mass between arbitrary
  coordinates, which leaves a general polytope.
- The point `z` stays in `K` by convexity. Only convexity of `Φ_t` (B5(b)) is used, at `z`, where
  the gradient is controlled by balance.
- No exact minimizer, no smoothness and no condition on `η` is needed.

The alternative repair through the exact step `w*` from `a t` also closes the induction: the
mixed sequence has balance `≤ 4ηT`, so `w* ≥ ψ` by B9, and `D_R(a (t+1), w*) ≤ ε`. But it needs
two extra things:
- existence and positivity of the exact minimizer on `K`;
- the extra condition `ε < (c₁/8) min{1, ψ^(2-ν)}`, from `D_r(y/2, y) ≥ c₁ y^(2-ν)/8`.

The threshold does not always imply this condition. It fails when `ν` is close to `1` and `η` is
of order `1`, for example `ν = 1.001`, `c₁ = c₂ = 1`, `η = 2`, `T = 1`, `d = 2`, where
threshold/condition `= 1.87` (check C10).

**B11. Lemma 42' (iterate lower bound).** Assume (E1) and (E2). Then `a t i ≥ ψ` for all
`t ≤ T` and all `i`.

*Proof.* Induction on `t`.
- `t = 0`: `q i ≥ m ≥ ψ`.
- Step `t → t+1` with `t < T`, assuming `a s ≥ ψ` for every `s ≤ t`:
  1. B10 (its hypothesis follows from the induction hypothesis) gives `a (t+1) ≥ ψ/2`.
  2. Now `a (s+1) ≥ ψ/2` for every `s < t+1`. B8 with `t+1`, `y = q` and `z = a (t+1)` gives
     `S_q(a (t+1)) ≤ (t+1)(η + δ)‖q - a (t+1)‖₁ ≤ T · 2η · 2 = 4ηT`.
  3. B9 gives `a (t+1) ≥ ψ`. ∎

**B12. Lemma 27' (OMD helper with the true strong convexity).** For `x, y ∈ K⁺`, `|ℓ i| ≤ 1` and
`η > 0`: `⟨ℓ, x - y⟩ - D_R(y, x)/η ≤ η/c₁`.

*Proof.* Let `m_i = max(x i, y i) ∈ (0, 1)`. By B4(d),
`D_R(y, x) ≥ (c₁/2) ∑ (y i - x i)²/m_i`. Since `∑ m_i ≤ ∑ x i + ∑ y i = 2`, Cauchy–Schwarz gives
`L := ‖x - y‖₁ ≤ √(∑ (y i - x i)²/m_i) · √2`. So `D_R(y, x) ≥ c₁ L²/4`, while
`⟨ℓ, x - y⟩ ≤ L`. Finally `L - c₁L²/(4η) ≤ η/c₁`, because
`η/c₁ - L + c₁L²/(4η) = (η/c₁)(1 - c₁L/(2η))² ≥ 0`. ∎

So `R` is `(c₁/2)`-strongly convex for `‖·‖₁` on the positive part of the simplex, and `c₁` with
Pinsker's inequality, which would give `η/(2c₁)`. It is not 1-strongly convex (erratum B-9).

**B13. One-round inequality.** Assume (E3) and (E4), let `t < T` with `a (t+1) ≥ ψ`, and let
`u ∈ K` be arbitrary (zero coordinates allowed). Then

```
η ⟨ℓ t, a (t+1) - u⟩ ≤ D_R(u, a t) - D_R(u, a (t+1)) - D_R(a (t+1), a t) + η².
```

*Proof.* Let `x = a (t+1)`, `h = u - x`, `γ₀ = 1/2`.
1. For `0 ≤ s ≤ γ ≤ 1/2`, `x + sh = (1-s)x + su ∈ K` by B2(c). Its coordinates are
   `≥ (1-s) x i ≥ x i/2 ≥ ψ/2 > 0`, and `< 1` by B2(a). So `r'' ≤ c₂(2/ψ)^ν =: M''` on every
   interval between `x i` and `x i + γ h i`.
2. By B4(a) and B2(d) (`∑ (h i)² ≤ ‖h‖₁²/2 ≤ 2`):
   `R(x + γh) - R(x) - γ⟨∇R(x), h⟩ ≤ M'' γ²` (`= γ² Q/2` with `Q = 2M''`).
3. B6 gives `⟨G_t(x), u - x⟩ ≥ -(2√(εM'') + 4ε)`. By (E3), `εM'' ≤ η⁴/16`, so
   `2√(εM'') ≤ η²/2`. By (E4), `4ε ≤ η²/2`. Hence `⟨G_t(x), u - x⟩ ≥ -η²`.
4. `⟨G_t(x), u - x⟩ = η⟨ℓ t, u - x⟩ + ⟨∇R(x) - ∇R(a t), u - x⟩`. The second term equals
   `D_R(u, a t) - D_R(u, x) - D_R(x, a t)` by B5(a). Rearrange. ∎

**B14. Theorem 6 (assembly).** Assume `d ≥ 2`, `0 < η ≤ 2` and the threshold. By B1, (E1)–(E4)
hold. By B11, `a t ≥ ψ` for every `t ≤ T`. For any `u ∈ K`:

```
Regret(u) = ∑_{t<T} [⟨ℓ t, a t - a (t+1)⟩ - D_R(a (t+1), a t)/η]
          + ∑_{t<T} [⟨ℓ t, a (t+1) - u⟩ + D_R(a (t+1), a t)/η]
          ≤ T η/c₁ + ∑_{t<T} [(D_R(u, a t) - D_R(u, a (t+1)))/η + η]       (B12, B13)
          = (D_R(u, q) - D_R(u, a T))/η + (1 + 1/c₁) η T.
```

This is the core form of 1.3. For `u ∈ K⁺`, B4(c) and B2(a) give `D_R(u, a T) ≥ 0`, which
yields 1.2. B0 covers `η > 2` and `d = 1`.

Constants used, summarized:
- `δ ≤ η` (from (E1), (E2)): balance per round `2η`, total `4ηT` with `‖q - x‖₁ ≤ 2`.
- `ψ` from B9 with `κ = 4ηT`.
- First-order error `η²` per round (from (E3), (E4)).
- Strong convexity: `η/c₁` per round.

**B15. Theorem 6' (extension).** Assume `ContinuousWithinAt r (Set.Ici 0) 0`. For `x ∈ (0, 1)`
and `s ∈ (0, x)`, B4(c) gives `r s ≥ r x + r' x (s - x)`. Let `s → 0⁺`:
`r 0 ≥ r x - r' x · x`, i.e. `D_r(0, x) ≥ 0`. With B4(c), this gives `D_R(u, y) ≥ 0` for every
`u ∈ K` and `y ∈ K⁺`.
- Case `η ≤ 2`: drop `-D_R(u, a T)` in B14.
- Case `η > 2`: B0, which uses `D_R(u, q) ≥ 0`. ∎

---------------------------------------------------------------------------------------------------

## 3. Errata (area B: Theorem 6 and the lemmas it uses)

Numbered `B-1, B-2, …` locally. The coordinator assigns the global `E` numbers in
`notes/paper-errata.md`. Locations refer to v2.

**B-1. Proof of Theorem 6 / Lemma 42, use of Lemma 25 on a polytope.**
- *Kind:* gap in the proof.
- *Error.*
  - Lemma 42 ("from Lemma 25, we know for start that `w_t^i ≥ ψ/2`") and the Section 5.2 sketch
    apply Lemma 25 (`not_too_far`) to a trajectory on a polytope `K`.
  - Lemma 25 is stated and proved for the simplex only. Its proof uses Lemma 24, whose comparison
    point `w̃` moves mass between arbitrary coordinates and is in general not in `K`.
- *Correction:* replace the step by Lemma 25-P (B10). The rest of the induction (B11) then
  closes.
- Whether Lemma 25's conclusion itself fails on polytopes is not settled. A random search over
  exact steps found shrink factors of at most `1.13` (check C9). The repair does not need it.

**B-2. Lemma 25 (`not_too_far`), constants.**
- *Kind:* wrong constant / missing hypothesis.
- *Error.* From Lemma 24 with `h ≥ c₁/(w_t^i)^ν ≥ c₁/w_t^i`, the proof writes
  `w_{t-1}^i ≥ w_t^i - 4c₁η w_t^i - √(c₁ ε w_t^i)`.
- *Correction.*
  - The correct bound is `w_t^i - 4η w_t^i/c₁ - √(2ε w_t^i/c₁)`: `c₁` is on the wrong side, and
    the `2` comes from B-3'.
  - The conclusion `w_{t±1}^i ≥ w_t^i/2` therefore needs `η ≤ c₁/16` and `ε ≤ c₁ w_t^i/32` (or
    `ε ≤ c₁ (w_t^i)^(2-ν)/32` using `h ≥ c₁/(w_t^i)^ν`).
  - The stated hypotheses `η ≤ 1/(16c₁)` and `ε ≤ (w_t^i)^ν/(16c₁)` do not imply these when
    `c₁ < 1`.
  - Typo: "`r''(w_t^i) ≥ w_t^i`" should read `≥ c₁/w_t^i`.
- Not used by the repaired proof.

**B-3'. Lemma 24 (`max step`).**
- *Kind:* wrong constant / missing hypothesis.
- *Error and correction.*
  - (i) Lemma 23 with `a = h/2`, `b = 2η`, `c = ε` gives `|w_t^i - w_{t+1}^i| < 4η/h + √(2ε/h)`,
    not `√(ε/h)`.
  - (ii) The bound `D_r ≥ (h/2)(Δ)²` with `h = min{r''(w_t^i), r''(w_{t+1}^i)}` needs `r''`
    monotone (Definition 18). For a ν-barrier, use `h = c₁/max{w_t^i, w_{t+1}^i}^ν`.
  - (iii) Typo: `D_R(w_t, ·)` uses the reversed argument order of Section 2.
- Not used by the repaired proof.

**B-3. Lemma 41 (`gradient_diff`).**
- *Kind:* false statement (for `ν > 2`) / wrong constant.
- *Error.*
  - It is stated as an equality, `r'(w₂) - r'(w₁) = c₁/w₁^(ν-1) - c₁/w₂^(ν-1)`, while the proof
    gives `≥`.
  - The integral is computed without its factor:
    `∫_{w₁}^{w₂} c₁ w^(-ν) dw = (c₁/(ν-1))(w₁^(1-ν) - w₂^(1-ν))`.
  - The inequality without the factor is false for `ν > 2`, for example for `r'' = c₁ x^(-ν)`
    (check C1).
- *Correction:* for `0 < w₁ ≤ w₂ < 1` (the paper's `0 ≤ w₁` must be strict),
  `r'(w₂) - r'(w₁) ≥ (c₁/(ν-1))(w₁^(1-ν) - w₂^(1-ν))`. See B3.

**B-4. Lemma 42 (`nonentropy_iterate_lb`) and the `ψ` of the Section 5.2 sketch.**
- *Kind:* false statement.
- *Error.* The claim `w_t^i ≥ ψ_paper = (c₁/(8ηTd + c₁(2d)^(ν-1)))^(1/(ν-1))` fails for `ν > 9`,
  already for exact OMD (`ε = 0`) on `K = Δ₂`. Counterexample:
  - `r'' = x^(-11)` (`ν = 11`, `c₁ = c₂ = 1`), `η = 1/16` (so `η ≤ 1/(16c₁)`), losses
    `ℓ_t = (1, -1)`, `T = 5·10⁶`;
  - then `w_T^1 = 0.209128 < ψ_paper = 0.209814` (check C2).
  - The exact dynamics is `x^(1-ν) - (1-x)^(1-ν) = 2(ν-1)ηt`, against the paper's
    `ψ^(1-ν) = 16ηT + 4^(ν-1)`.
- *Correction:* `ψ = ((2d)^(ν-1) + 8(ν-1)ηTd/c₁)^(-1/(ν-1))` (B9, B11). It is the consequence of
  B-3, and the corrected `ψ` holds in the counterexample.
- The corrected `ψ` is larger than the paper's when `ν < 2`, and smaller by a factor
  `(ν-1)^(-1/(ν-1)) ∈ [e^(-1/e), 1)` when `ν > 2` and `ηTd/c₁` dominates.

**B-5. Threshold of Theorem 6 versus Lemma 42.**
- *Kind:* wrong constant (threshold not supported by the proof).
- *Error.* Lemma 42 says "the assumptions of the theorem are that
  `ε ≤ η⁴ min{c₂, 1/c₂}(ψ/2)^ν`". The theorem's threshold equals
  `η⁴ min{c₂, 1/c₂} 2^(-ν/(ν-1)) ψ_paper^ν`. This is `≤ η⁴ min{…}(ψ_paper/2)^ν` only when
  `ν ≤ 2`. For `ν > 2` the theorem allows a larger `ε`, by the factor `2^(ν - ν/(ν-1))`
  (`2.83` at `ν = 3`, check C3).
- *Correction:* the threshold of 1.1.

**B-6. Lemma 11 (`trajectory diff`), main text and appendix restatement.**
- *Kind:* wrong constant.
- *Error.*
  - (i) On `[ŵ_t, ŵ_t + ψv]` with `‖v‖₁ = 1`, the coordinates go down to `ψ/2`, since
    `|v^i| ≤ 1/2`. The effective smoothness is therefore `c₂/(ψ/2)^ν`, not `c₂/ψ^ν`.
  - (ii) The induction step adds `√(2c₂ε/ψ^ν)` per round, but the statement claims
    `√(c₂ε/ψ^ν)`.
  - (iii) The main text puts the lower bound `ψ` on the exact trajectory `w_t`. The appendix puts
    it on `ŵ_t`, which is what the proof needs.
  - (iv) The exact trajectory `γ` plays no role: only `η⟨ℓ_{t-1}, v⟩` is used.
- *Correction:* for `‖v‖₁ = 1`,
  `B̂^v(t₁,t₂) ≤ η⟨ℓ_{t₁:t₂-1}, v⟩ + (t₂-t₁)(√(2^ν c₂ ε/ψ^ν) + 2ε/ψ)` (B7, B8, with
  `∑ (v^i)² ≤ 1/2`). Under the side condition `ε ≤ 2^(ν-2) c₂ ψ^(2-ν)`, the term `2ε/ψ` can be
  dropped.

**B-7. Lemma 42, auxiliary steps.**
- *Kind:* missing hypothesis.
- *Error.* The steps "`ε ≤ ηψ^ν`" (needs `η³ ≤ 2^ν`), "`ε ≤ c₂ψ/4`" (needs
  `η⁴(ψ/2)^(ν-1) ≤ 1/2`) and "`T√(c₂ε(2/ψ)^ν) ≤ ηT`" (needs `η ≤ 1`) do not follow from
  `η ≤ 1/(16c₁)` when `c₁ < 1/16`.
- *Correction:* none needed in the repaired proof. The case `η > 2` is trivial (B0), and B1
  handles `η ≤ 2`.

**B-8. Hypothesis `η ≤ 1/(16c₁)` of Theorem 6.**
- *Kind:* none (generalization). It is listed because the statement changes.
- It is only used through Lemma 25, where the right condition would be `η ≤ c₁/16` (B-2). The
  repaired proof needs no condition on `η`.

**B-9. The `O(ηT)` term and Lemma 27 (`OMD Helper`).**
- *Kind:* wrong constant / missing hypothesis.
- *Error.*
  - The proof applies Lemma 27, which assumes `R` 1-strongly convex (the standing assumption of
    Section 2). A ν-barrier is only `(c₁/2)`-strongly convex for `‖·‖₁` on the simplex (`c₁` via
    Pinsker) (B12).
  - The constant hidden in `O(ηT)` must depend on `c₁`. Counterexample to every numerical
    constant `C`, within the paper's hypotheses (check C4):
    - `T = 1`, `ε = 0`, `K = Δ₂`, `r = -c log x` (`ν = 2`, `c₁ = c₂ = c`), `η = √c`
      (`≤ 1/(16c)` for `c ≤ 0.15`), `ℓ₁ = (1, -1)`, `w = (0.01, 0.99)`;
    - then `Regret(w) = 0.98` while `D_R(w, w₁)/η = 3.2·10⁻⁴` for `c = 10⁻⁸`, which forces
      `C ≥ 9796`, and `C → ∞` as `c → 0`.
- *Correction:* `Regret(u) ≤ D_R(u, w₁)/η + (1 + 1/c₁) η T` (1.2).

**B-10. Comparators with zero coordinates; Definition 1 versus its examples.**
- *Kind:* missing hypothesis.
- *Error.* Definition 1 takes `r : [0,1] → ℝ` real-valued, which excludes the log barrier that it
  lists. For a boundary comparator, `D_R(w, w₁)` is then `+∞` (paper) or junk (Lean). With the
  Lean junk `-log 0 = 0`, the bound is false (example in 1.3).
- *Correction:* the headline for `u ∈ K⁺`, Theorem 6' under right-continuity at `0`, and the core
  form for all `u ∈ K` (1.3).

**B-11. Lemma 10 (`polytope balance`), indices.**
- *Kind:* typo.
- *Error.* The round-`t'` optimality condition links `w_{t'-1}` and `w_{t'}`. Summing over
  `t' ∈ [t₁, t₂]` gives `η⟨ℓ_{t₁-1:t₂-1}, v⟩`, not `B^v(t₁, t₂)`.
- *Correction:* `B^v(t₁,t₂) = η⟨ℓ_{t₁:t₂-1}, v⟩`, summing over `t' ∈ [t₁+1, t₂]`. In Lean,
  `B^v(s, t) = η⟨L_{[s,t)}, v⟩`.

**B-12. Final computation of the proof of Theorem 6.**
- *Kind:* gap in the proof.
- *Error.*
  - It applies Lemma 22 with `w = w*` and `β = c₂/ψ^ν`, which requires the smoothness bound on
    the whole segment `[ŵ_{t+1}, w*]`. But `w*` (typically a vertex of `K`) has zero coordinates,
    where `r''` is unbounded, so the hypothesis of Lemma 22 fails.
  - The case `2ε ≥ ‖w - ŵ‖√(2βε)` of Lemma 22's proof even uses the full segment (`γ = 1`).
- *Correction:* the localized Lemma 22' (B6), applied with `γ₀ = 1/2` (B13), gives
  `⟨∇φ_t(ŵ_{t+1}), w - ŵ_{t+1}⟩ ≥ -(2√(2^ν c₂ ε/ψ^ν) + 4ε)`.

**B-13. Lemma 12 (`balance to gradient UB`).**
- *Kind:* typo.
- The appendix statement and its proof are correct, including the case `v^ī ≤ 1/2d`.
  - The main-text form `-r'(w_t^i) ≤ 4kd - r'(1/2d)` follows from the appendix form, because
    `k ≥ 0` and `r'` is monotone.
  - The proof cites "Lemma 10" where the definition of `k`-balance is meant.
  - Only the single direction `v = w₁ - w_t` (`‖v‖₁ ≤ 2`) is used.
- Lemma 31 is correct (it needs `v ≠ 0`; "greater than 0" should be "`≥ 0`").
- A cleaner form: each term `(r'(1/d) - r'(w_t^i))(1/d - w_t^i)` is `≥ 0` and `≤ 2k` (B9).

**B-14. Minor typos in the general lemmas used.**
- *Kind:* typo.
- Definitions 16, 17: `argmin_{w ∈ Δ_d}` should be over `K`, and `D_R(w_{t-1}, w)` should be
  `D_R(w ‖ w_t)`.
- Lemma 22: the last display of the proof misses a minus sign
  (`≥ -‖w - ŵ‖√(2βε)`).
- Lemma 30: "`w - αv ∈ Δ_d`" should be "`w* - αv ∈ K`", and `∇f(ŵ)` should be `∇f(w*)`.

---------------------------------------------------------------------------------------------------

## 4. Numerical checks

Scripts are in
`/tmp/claude-663481/-home-rdegenne-Documents-Lean-Schlisselberg2026Hidden/7ad2edfa-b559-4fea-932a-1aff1e8cf05b/scratchpad/barrier-polytope/`
(run with `python3 -I`; numpy 2.4.3, scipy 1.18.0, mpmath 1.4.1). Each output is saved next to its
script as `*.out`.

- **C1 (`check1_closed_form.py`)**: Lemma 41 as written versus corrected, for `r'' = x^(-ν)`,
  `w₁ = 0.01` and `w₂ = 0.5`.
  - The paper's inequality fails at `ν = 3` (`4998 < 9996`) and at `ν = 11`.
  - The corrected inequality holds with equality.
- **C2 (same script)**: Lemma 42 counterexample: exact OMD on `Δ₂` with `ν = 11` (60-digit
  mpmath, KKT residuals `< 10⁻⁵⁴`).
  - `T = 5·10⁶`: `a_(T-1)^1 = 0.2091279 < ψ_paper = 0.2098141`.
  - `T = 10⁷`: `0.1951232 < 0.1975465`.
  - The corrected `ψ` (`0.1695` and `0.1583`) holds.
- **C3 (same script)**: the ratio (theorem threshold)/(Lemma 42 assumption) equals
  `2^(ν - ν/(ν-1))`: `0.036` at `ν = 1.2`, `1` at `ν = 2`, `2.83` at `ν = 3`, `13.5` at `ν = 5`.
- **C4 (same script)**: the `c₁`-dependence counterexample of B-9.
  - The numerical constant needed is `6.6`, `95` and `9797` for `c = 10⁻²`, `10⁻⁴` and `10⁻⁸`.
  - The corrected bound `D/η + (1 + 1/c₁)η` holds in all three cases.
- **C5 (same script)**: `ψ` and the thresholds, ours versus the paper's.
  - Ratio ours/paper `≈ 0.50` at `ν = 1.5`, `1/64` at `ν = 2`, `10⁻³` at `ν = 3`,
    `2.7·10¹²` at `ν = 1.1`, and `1.3·10⁻⁸` at `ν = 11`.
- **C6 (`check2_lemmas.py`)**: randomized tests of B4(d)/B12, B3, B5(b), B6/B7, B6/B13, B9 and
  B10 (inequality of steps 1–3).
  - Setup: 1200 random instances. Polytopes are `K ⊆ Δ_d` with `d ∈ [3, 6]` and up to 3 extra
    equality constraints, with random interior points, `η ∈ {0.01, …, 2}`, losses in
    `[-1, 1]^d` and `ε` the actual suboptimality of a perturbed exact step.
  - The barrier `r'' = x^(-ν)(1.5 + 0.5 sin(20 log x))` has `c₁ = 1`, `c₂ = 2`, a non-monotone
    `r''`, closed-form `r` and `r'`, and `ν ∈ {1.2, 1.5, 2, 3}`.
  - The minimal slacks are all positive: B5(b) `1.4e-5`, B7 `2.4e-6`, B13-form `6.0e-6`, B10
    `6.3e-7`, B12 `8.0e-3`, B3 `5.9e-5`, B9 `4.7e-2`.
- **C10 (`check5_exact_step_repair.py`)**: whether the corrected threshold implies the extra
  condition of the alternative exact-step repair (see B10). Results in 4.1.
- **C7/C8 (`check3_trajectories.py`)**: full ε-approximate trajectories on the polytope
  `K = {w ∈ Δ₄ : w¹ + 2w² - w³ - 2w⁴ = 0}`, which contains the uniform point.
  - The adversary spends the whole ε budget pushing the smallest coordinate down.
  - Setup: `ν ∈ {1.5, 2, 3}`, `η ∈ {0.1, 0.5}`, `T ∈ {50, 200}`, `ε ∈ {0, threshold,
    10⁶·threshold}`, and constant, switching and random losses.
  - We check `min_t,i a t i ≥ ψ`, the headline bound against positive comparators near the LP
    optimum, and the core form. RESULTS: see 4.1.
- **C9 (`check4_halving_search.py`)**: search for a one-step halving `w_{t+1}^i < w_t^i/2` under
  EXACT OMD on random polytopes (Lemma 25's conclusion off the simplex).
  - Setup (reduced run): `d ∈ {4, 5}` with 1–2 extra constraints, starting points
    `(1-τ)V + τp` near vertices `V` (coordinates down to `10⁻⁷`), all `2^d` sign losses,
    `η = 1/16`, and `r'' = x^(-ν)` with `c₁ = c₂ = 1`.
  - RESULTS: see 4.1.

### 4.1 Results of C7–C10

- **C7/C8** (108 runs, `check3_trajectories.out`): no violation.
  - Over all runs, `min a/ψ = 3.59`. The smallest values occur at `ν = 3`. At `ν = 1.5`,
    `min a/ψ ≥ 300`: the bound `ψ` is very conservative for small `ν`.
  - `min (bound − regret) = 16.9` and `min (core − regret) = 9.37`.
  - Even at `ε = 10⁶ ×` threshold, no run left the guarantees.
  - The adversary's effect at the threshold is invisible: the iterates agree with the exact ones
    to `≈ 10⁻⁵` relative. This is a sanity check of the statement, not a test of its sharpness.
- **C9** (`check4_halving_search.out`, reduced run: 15 polytopes per `ν`, `d ∈ {4, 5}`, 1–2
  extra constraints, 3 vertices, `τ ∈ {10⁻², 10⁻⁴, 10⁻⁷}`, all sign losses): no one-step halving
  was found.
  - The largest shrink factors `a^i / w*^i` are `1.127` (`ν = 1.2`), `1.014` (`ν = 1.5`),
    `1.0006` (`ν = 2`) and `1.0000` (`ν = 3`), all at the least extreme `τ = 10⁻²`.
  - So the failure of Lemma 25 on polytopes is a gap in the proof. No counterexample to its
    conclusion is known. A heuristic quadratic analysis suggests that large relative moves need
    several simultaneously tiny coordinates and `ν < 2`. It was not pursued, since the repair
    does not need Lemma 25.
- **C10 (`check5_exact_step_repair.py`)**: on a grid of `(ν, c₁ = c₂, η, T, d)`, the corrected
  threshold fails to imply the condition `ε < (c₁/8) min{1, ψ^(2-ν)}` of the exact-step repair
  in 9 cases, all with `ν ∈ {1.001, 1.01}` and `η = 2`. The largest ratio is `11.4`, at
  `ν = 1.001`, `c₁ = 0.1`, `T = 1`, `d = 2`.

---------------------------------------------------------------------------------------------------

## 5. Points of uncertainty

- **Lean form of the barrier hypothesis.** The blueprint uses, on `(0, 1)` only: differentiability
  of `r` and `r'`, the two-sided bound on `r'' = deriv (deriv r)`, monotonicity of `r'` (from
  `r'' > 0`) and the Taylor bounds B4 (from the sign of the second derivative of an auxiliary
  function). No continuity at `0` is used, except in Theorem 6'. If the project instead states
  the barrier with `ContDiffOn ℝ 2 r (Set.Ioo 0 1)`, the same facts follow.
- **Whether Lemma 25's conclusion fails on polytopes** (rather than only its proof): see C9. The
  repaired proof does not depend on it.
- **Sharpness.** The threshold is not optimized: `4^(ν+2)` and the `max 1 c₂` are margins. Whether
  the paper's original threshold suffices for the regret bound (by a different proof) is not
  settled. Its proof does not support it for `ν > 2` (B-4, B-5).
