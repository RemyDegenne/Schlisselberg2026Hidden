# Theorem 8 (`thm:lb_nonsimplex`): corrected statement, explicit constants, blueprint

Area D of the constants review of [SSKM26] (arXiv:2511.22283v2). Sources: Theorem 8 (main text,
Section 4.2), its proof in the appendix section "Proof of Theorem 8" (`sec:polytope lower bound`:
Lemmas 43–48, Theorem 49), Lemma 10 (`lem:polytope balance`). Conventions: `notes/modelling.md`
(rounds from `0`, `a 0 = w₁`, regret over rounds `t < T`, ε-approximate steps
`η⟨ℓ, x⟩ + D(x, a) ≤ η⟨ℓ, b⟩ + D(b, a) + ε` for all `b ∈ K`, positive iterates, `negEntropy`,
i.i.d. losses on a probability space). Numerical checks: scripts in
`/tmp/claude-663481/-home-rdegenne-Documents-Lean-Schlisselberg2026Hidden/7ad2edfa-b559-4fea-932a-1aff1e8cf05b/scratchpad/polytope-lower/` (Section 5).

## 0. Verdict

The construction is sound and the statement is true once corrected, with **both** terms of the
paper's bound (`D_R(w, w₁)/η` and `T√(η/log(1/ε))`) and explicit constants. The paper's proof
has several gaps; the main ones:

- the hardness event `E` of Lemma 45 does not have probability `Ω(1)` by the paper's argument:
  `P(G ≤ 0) = Φ(−√(3d/(m+1))) ≈ 5·10⁻⁵` while the union bound over the rounds only controls the
  second part of `E` up to probability `1/2`; the per-round Gaussian bound is also misstated;
- Lemma 47's inequalities are inverted (its conclusion `e^{m/8}` is useless as written; with the
  signs fixed it gives `e^{−m/8}`);
- Lemma 48's proof that the exact step increases the first coordinates is wrong;
- Theorem 49 computes the expected loss on `E`, although `E` depends on the losses of the same
  rounds, and ignores `Eᶜ`; the `D_R(w, w₁)/η` term of Theorem 8 is not proved anywhere;
- the quantifier order and the range "for any `ε > 0`" are wrong; `d ≤ 1/η` is assumed without
  proof ("there's a known lower bound for Tη").

The corrected proof below replaces the paper's event `{G ≤ 0}` by the median event
`{G ≤ E[G]}` (probability `1/2` by symmetry), proves a sharper Lemma 47 that tolerates
`ηG = O(1)`, and replaces the paper's modification of the exact step (Lemma 48) by an explicit
"frozen" step whose suboptimality is bounded in closed form. The whole trajectory is then an
explicit, measurable, predictable function of the losses, and is ε-approximate for **every**
loss sequence (no event needed for validity).

Two further findings matter for the formalization:

- **The Gaussian noise is not needed.** With the sharper Lemma 47 the same proof works for the
  constant losses obtained by replacing every Gaussian by its mean (Variant 8-C, deterministic,
  constant `1` instead of `1/4`, no condition on `T`), and for bounded Rademacher noise
  (Variant 8-B, losses in `[−1, 1]^d` as in Theorem 7, constant `1/2`, no condition on `T`).
  Both are much easier to formalize; 8-C still proves the paper's existential claim ("there
  exists a distribution of losses") with a Dirac law. The Gaussian version 8-G is kept as the
  default as instructed; I recommend switching (decision for the user, Section 6).
- **The dimension must be pinned in the Lean statement.** A statement of the form "∃ polytope
  `K ⊆ Δ_d` (any `d`) …" is trivially implied by Theorem 35 (`thm:dimension lower bound`): in
  dimension `d ≥ η²e^η/ε`, staying at the uniform point is ε-approximate for constant losses and
  has regret `T(1 − 1/d) ≥ T/2`. The content of Theorem 8 is that `d = O(log(1/ε))`. The Lean
  statement must fix `K = K_m` (or at least assert `d ≤ 100 log(1/ε)`).

## 1. Objects

Parameters: `η > 0`, `ε ∈ (0, 1)`, `T ∈ ℕ`. Put

- `L := log(1/ε)`, `m := ⌈16 L⌉₊` (natural number), `d := 5m + 2`;
- `μ := √(η d)` (the mean loss of coordinate `P`);
- `τ := ⌈3/η⌉₊` (length of the exact phase).

**Index type.** `α_m` with `5m + 2` elements, written (paper's 1-based index in brackets)
`X i` [`i`], `Y k i` for `k ∈ {1, 2, 3}` [`km + i`], `Z i` [`4m + i`] (`i < m`), `P` [`5m + 1`],
`Q` [`5m + 2`]. Suggested Lean type: an inductive with these constructors, or
`(Fin m × Fin 5) ⊕ Fin 2`; `d = Fintype.card α_m`.

**Polytope** `K_m = {w | (∀ j, 0 ≤ w j) ∧ A w = b}` with the paper's `A` (`4m + 1` rows:
`A_i = e_{Y1 i} + e_{Y2 i} − 2e_{Y3 i}`, `A_{m+i} = e_{Y1 i} − e_{Y2 i}`,
`A_{2m+i} = e_{X i} + 3e_{Y1 i} + e_{Z i}`, `A_{3m+i} = e_{Z i} − e_P`, `A_{4m+1} = e_P + e_Q`)
and `b = A u`, `u = fun _ ↦ 1/d` the uniform point.

**Comparator** `w*`: `w*(X i) = 5/d`, `w*(Q) = 2/d`, all other coordinates `0` (the paper's
`w₁ + Σ_i v_i/d`). `D_R(w*, u) = (5m log 5 + 2 log 2)/d ∈ [1.57, log 5]` for `m ≥ 12`.

**Loss laws** (product measures on `α_m → ℝ`, coordinates independent):

- 8-G (paper): `X ↦ δ₀`, `Y ↦ δ₁`, `Z ↦ N(0, 1)`, `P ↦ N(μ, 1)`, `Q ↦ δ₀`;
- 8-B (bounded): `X ↦ δ₀`, `Y ↦ δ₁`, `Z ↦ ½δ₋₁ + ½δ₁`, `P ↦ δ_μ`, `Q ↦ δ₀` (losses in `[−1, 1]`);
- 8-C (deterministic): the constant loss `ℓ°`: `X ↦ 0`, `Y ↦ 1`, `Z ↦ 0`, `P ↦ μ`, `Q ↦ 0`.

For a loss vector `ℓ` write `S(ℓ) := Σ_i ℓ(Z i) + ℓ(P)`. In all three laws `E[S] = μ`;
in 8-G, `S ~ N(μ, m + 1)`.

**Curve of iterates.** For `n ∈ ℕ` and `q ∈ (0, 2/d)` let `E_n := e^{ηn}` and

- `y_n(q) := (3/d + q)/(E_n + 3)`, `x_n(q) := E_n y_n(q)`, `z(q) := 2/d − q`;
- `W_n(q)`: `X i ↦ x_n(q)`, `Y k i ↦ y_n(q)`, `Z i ↦ z(q)`, `P ↦ z(q)`, `Q ↦ q`;
- `f_n(q) := m log x_n(q) + log q − (m + 1) log(2/d − q)`;
- `F_n : ℝ → (0, 2/d)` the inverse of `f_n` (Lemma 8.4);
- `ρ_n := 3E_n/(E_n + 3)` (so `x_n(q) ≥ ρ_n/d`);
- `h(r) := e^{−r} − 1 + r ≥ 0`.

The paper's coefficients: `q = 1/d + α^{m+1}`, `y_n(q) = 1/d − α^i`.

**Trajectory.** For a loss sequence `ℓ`, with `S_n := S(ℓ n)`, define `q_0 := 1/d` and

- `r_n := f_{n+1}(q_n) − f_n(q_n) − ηS_n = m log(x_{n+1}(q_n)/x_n(q_n)) − ηS_n`;
- `q_{n+1} := q_n` if `τ ≤ n` and `q_n h(r_n) ≤ ε` ("frozen step"),
  `q_{n+1} := F_{n+1}(f_n(q_n) + ηS_n)` otherwise ("exact step");
- `a n := W_n(q_n)`.

`q_n` is a measurable function of `(S_0, …, S_{n−1})`, hence `a n = A_n(ℓ 0, …, ℓ (n−1))` for a
measurable `A_n : (Fin n → α_m → ℝ) → α_m → ℝ` that depends on `(η, ε)` only (not on `T`).
(Variant of the switch with the same proofs: `q_n e^{η(m + |S_n|)} ≤ ε`.)

## 2. Corrected statements

### Theorem 8-G (default: the paper's Gaussian losses)

Let `η > 0`, `0 < ε ≤ 1/2`, `T ∈ ℕ`, and `L, m, d, K_m, u, w*, ν^G, A_n` as in Section 1.

1. *(Validity, no hypothesis.)* For every loss sequence `ℓ : ℕ → α_m → ℝ` with
   `ℓ t (X i) = 0`, `ℓ t (Y k i) = 1`, `ℓ t Q = 0` for all `t, k, i` (the `Z`- and
   `P`-coordinates are arbitrary), the sequence `a t := A_t(ℓ 0, …, ℓ (t−1))` has `a 0 = u`,
   `a t ∈ K_m`, all coordinates of `a t` positive, and `a (t+1)` is an ε-approximate mirror
   descent step on `K_m` from `a t` for the loss `ℓ t` (negative entropy, learning rate `η`),
   for every `t`.
2. *(Regret.)* Assume `(H1) η d ≤ 1` and `(H2) ε T ≤ 1`. For every probability space `(Ω, P)`
   and measurable `ℓ : ℕ → Ω → α_m → ℝ`, independent over the rounds (`iIndepFun`), with every
   `ℓ t` of law `ν^G`, and `a t ω := A_t(ℓ 0 ω, …, ℓ (t−1) ω)`:

   `E[regret ℓ a w* T] ≥ (1/4) T √(η/d)`,

   and if moreover `(H3) η T ≥ 1`:

   `E[regret ℓ a w* T] ≥ D_R(w*, u)/(6η) + (1/4) T √(η/d)`.
3. *(Paper's form.)* `d ≤ 100 log(1/ε)`, hence `(1/4) T √(η/d) ≥ (1/40) T √(η / log(1/ε))`;
   and `100 η log(1/ε) ≤ 1` implies `(H1)`. So under `0 < ε ≤ 1/2`, `100 η log(1/ε) ≤ 1`,
   `εT ≤ 1`, `ηT ≥ 1`:
   `E[Regret(w*)] ≥ D_R(w*, w₁)/(6η) + (1/40) T √(η / log(1/ε))`.

Quantifier order: `∀ η ε` (in range) `∃ K` (depending on `ε`) and a law (depending on `ε, η`)
`∃` a trajectory map (depending on `ε, η`) and `w* ∈ K` such that `∀ T` (in range) the bound
holds. In item 2, `a` is ε-approximate almost surely (item 1 applies to every `ω` outside the
null set where a constant coordinate is wrong); a formalization may instead build the losses so
that the constant coordinates hold everywhere.

Range of parameters (a sufficient form: `e^{−1/(100η)} ≤ ε ≤ min(1/2, 1/T)` and `T ≥ 1/η`),
and what happens outside it:

- `ε ≥ 1`: `log(1/ε) ≤ 0`, the paper's bound is meaningless. `ε ∈ (1/2, 1)`: excluded for the
  constants; as `ε → 1` the paper's bound `T√(η/log(1/ε))` exceeds `2T`, the largest possible
  regret for losses in `[−1, 1]^d`, so "for any `ε > 0`" cannot hold with a fixed constant.
- `ε T > 1` (8-G only): not covered. Monotonicity (an `ε₀`-approximate trajectory is
  ε-approximate for `ε ≥ ε₀`) gives the bound with `ε₀ = 1/T` in place of `ε`, i.e.
  `T√(η/log T)/40`, not the claimed `T√(η/log(1/ε))`. The proof actually only needs
  `8T ≤ exp(L² d)` (implied by `εT ≤ 1`); 8-B and 8-C need no condition on `T`.
- `η d > 1` (roughly `ε < e^{−1/(100η)}`): not covered. The paper's reduction ("there's a known
  lower bound for Tη") is unproven; there the claimed term is at most `10 η T`.
- `η T < 1`: the `D_R/η` term fails for this construction when `ηT < 0.26` (the expected
  regret is at most `T`: `3m y_t ≤ 15m/(4d) < 3/4` and `μ z_t ≤ 2/d`, while
  `D_R(w*, u)/(6η) ≥ 0.26/η`); the `T√` term holds without `(H3)`.

### Variant 8-B (bounded losses, recommended alternative)

Same objects with the law `ν^B` (losses in `[−1, 1]^{α_m}`). Assume `0 < ε ≤ 1/3`
(so `m ≥ 18`, `d ≥ 92`) and `(H1)`; **no condition on `T`**. Then item 1 holds, and

`E[regret ℓ a w* T] ≥ (1/2) T √(η/d) ≥ (1/20) T √(η/log(1/ε))`, plus `D_R(w*, u)/(6η)` under
`(H3)`.

Needs only: symmetry of the law of a sum of independent Rademacher variables, independence of
rounds for `E[S_t z_t] = μ E[z_t]`. No Gaussian measure theory. Same loss class as Theorem 7.

### Variant 8-C (deterministic losses)

Same objects, the constant loss sequence `ℓ t = ℓ°`; assume `0 < ε ≤ 1/3` and `(H1)`. Then
item 1 holds and

`regret ℓ° a w* T ≥ T √(η/d) ≥ (1/10) T √(η / log(1/ε))`, plus `D_R(w*, u)/(6η)` under `(H3)`.

With the Dirac law `δ_{ℓ°}` (i.i.d. trivially) this proves the paper's existential claim as
stated ("a distribution of losses"). No probability at all.

### Shape for Lean

- Fix `K = K_m` (explicit `A`, `b`), `u`, `w*` and the law as definitions; never quantify
  `∃ K` over all dimensions (trivial by Theorem 35, see Section 0).
- The trajectory as `∃ A : (t : ℕ) → (Fin t → α_m → ℝ) → (α_m → ℝ), (∀ t, Measurable (A t)) ∧ …`
  (play `t` depends on the losses of rounds `< t`), with item 1 as a deterministic statement
  and item 2 for every probability space and every i.i.d. sequence with the given law.
- `regret ℓ a w* T = Σ_{t<T} (⟨ℓ t, a t⟩ − ⟨ℓ t, w*⟩)`; `D_R = bregDiv negEntropy w* u` with
  the gradient `h ↦ Σ_j log (u j) · h j`.
- Relation to the paper: corrects Theorem 8 (quantifier order, ranges, constants, both terms
  proved). With 8-C: corrects it, the distribution being a Dirac mass.

## 3. Blueprint

Standing facts (Lemma 8.0) are used everywhere without citation. "8-G only" marks the steps
that differ in the variants; Section 3.9 lists the variant deltas.

### 3.1 Parameters

**Lemma 8.0 (parameter facts).** Let `0 < ε ≤ 1/2` and `η d ≤ 1`. Then
(a) `L ≥ log 2`, `m ≥ 12`, `d ≥ 62`, `m ≥ 16 L` hence `e^{−m/4} ≤ ε⁴`;
(b) `0 < μ ≤ 1`, `η ≤ 1/62`, `η m ≤ m/d < 1/5`;
(c) `3 ≤ ητ < 3 + η ≤ 3.02` (so `ητ ≤ 4`);
(d) `d ≤ 100 L`;
(e) if `τ < T` and `εT ≤ 1` then `ε < 1/τ ≤ η/3 ≤ 1/(3d) ≤ 1/186`.

*Proof.* (a) `16 log 2 = 11.09…`, so `m ≥ 12`; `e^{−m/4} ≤ e^{−4L} = ε⁴`.
(b) `ηd ≤ 1`. (c) `τ = ⌈3/η⌉ ∈ [3/η, 3/η + 1)`. (d) `m < 16L + 1`, so `d < 80L + 7 ≤ 100L`
since `L ≥ 0.35`. (e) `ε ≤ 1/T < 1/τ ≤ η/3`. ∎

### 3.2 The polytope

**Lemma 43 (coordinates of `K_m`; replaces the paper's kernel basis).** `w ∈ K_m` iff `w ≥ 0`
and for all `i`: `w(Y1 i) = w(Y2 i) = w(Y3 i)`, `w(Z i) = w(P)`,
`w(X i) + 3 w(Y1 i) + w(Z i) = 5/d`, and `w(P) + w(Q) = 2/d`.
*Proof.* `b = A u` has entries `0` (rows `A_i`, `A_{m+i}`, `A_{3m+i}`), `5/d` (`A_{2m+i}`),
`2/d` (`A_{4m+1}`). Row `A_{m+i}` gives `Y1 = Y2`, then `A_i` gives `2Y1 − 2Y3 = 0`; the other
rows are the remaining equations. ∎
(The paper's Lemma 43 — `v_1, …, v_{m+1}` is a basis of `ker A`, `rank A = 4m + 1` — is true
(checked numerically) but not needed.)

**Lemma 44 (`K_m ⊆ Δ`, `u, w* ∈ K_m`).** For `w ∈ K_m`,
`Σ_j w j = Σ_i (w(X i) + 3w(Y1 i) + w(Z i)) + w(P) + w(Q) = 5m/d + 2/d = 1`. `u` and `w*`
satisfy Lemma 43. `⟨ℓ, w*⟩ = 0` whenever `ℓ(X i) = 0 = ℓ(Q)` (the other coordinates of `w*`
vanish). ∎

**Lemma 8.1 (the curve).** For `q ∈ (0, 2/d)`: `W_n(q) ∈ K_m`, all its coordinates are positive,
`W_0(1/d) = u`; `x_n(q) = E_n y_n(q)`; `x_n(q) ≥ ρ_n/d`; and
`0 ≤ log(x_{n+1}(q)/x_n(q)) ≤ η`.
*Proof.* `x + 3y + z = (E_n + 3)y + z = 3/d + q + 2/d − q = 5/d`, `z + q = 2/d`; positivity from
`0 < q < 2/d`. `x_n(q) ≥ E_n (3/d)/(E_n + 3) = ρ_n/d`.
`x_{n+1}/x_n = e^η (E_n + 3)/(e^η E_n + 3) ∈ [1, e^η]`. ∎

### 3.3 Steps

Write `φ(b) := η⟨ℓ, b⟩ + D(b, a)` for the objective of the step from `a` with loss `ℓ`, and
`δ(s, c) := s log(s/c) − s + c` for `s ≥ 0`, `c > 0` (with `0 log 0 = 0`); `δ ≥ 0`.

**Lemma 8.2 (three-point form of the gap; cf. Lemma 26).** For `a, x ∈ K_m` with positive
coordinates and `b ∈ K_m`:
`φ(b) − φ(x) = ⟨ηℓ + log x − log a, b − x⟩ + D(b, x)` and `D(b, x) = Σ_j δ(b j, x j)`.
*Proof.* Algebra: `D(b, a) − D(x, a) = R(b) − R(x) − ⟨log a, b − x⟩` and
`D(b, x) = R(b) − R(x) − ⟨log x, b − x⟩`, `R = negEntropy`. ∎

**Lemma 8.3 (residual on `K_m`).** Let `a = W_n(q)`, `x = W_{n+1}(q')` (`q, q' ∈ (0, 2/d)`), `ℓ`
with `ℓ(X i) = 0`, `ℓ(Y k i) = 1`, `ℓ(Q) = 0`, `S = S(ℓ)`, `b ∈ K_m`. Then
`⟨ηℓ + log x − log a, b − x⟩ = (f_{n+1}(q') − f_n(q) − ηS)·(b(Q) − q')`.
*Proof.* Let `g = ηℓ + log x − log a`. Coordinates: `g(X i) = γ_X := log(x'/x)`,
`g(Y k i) = γ_Y := η + log(y'/y)`, `g(Z i) = ηℓ(Z i) + γ_Z`, `g(P) = ηℓ(P) + γ_Z` with
`γ_Z := log(z'/z)`, `g(Q) = γ_Q := log(q'/q)`. For `b ∈ K_m` write `y_b i := b(Y1 i)`,
`z_b := b(P)`; by Lemma 43, `b(X i) − x' = −3(y_b i − y') − (z_b − z')` and
`b(Q) − q' = −(z_b − z')`. Hence
`⟨g, b − x⟩ = 3(γ_Y − γ_X) Σ_i (y_b i − y') + (z_b − z')(ηS + (m+1)γ_Z − mγ_X − γ_Q)`.
`γ_Y − γ_X = η − (log(x'/y') − log(x/y)) = η − (η(n+1) − ηn) = 0` (Lemma 8.1), and
`mγ_X + γ_Q − (m+1)γ_Z = f_{n+1}(q') − f_n(q)`; finally `z_b − z' = −(b(Q) − q')`. ∎

**Lemma 8.4 (`f_n`, `F_n`).** `f_n` is continuous and strictly increasing on `(0, 2/d)`, tends to
`−∞` at `0⁺` and to `+∞` at `(2/d)⁻`; so `F_n := f_n⁻¹ : ℝ → (0, 2/d)` exists, is strictly
increasing (hence measurable). `f_0(1/d) = 0` and `f_n(1/d) = m log(4E_n/(E_n + 3)) ≥ 0`.
*Proof.* The three terms of `f_n` are increasing in `q`; `log q → −∞`,
`−(m+1) log(2/d − q) → +∞`, the others stay bounded (`3/d + q ∈ (3/d, 5/d)`). `x_n(1/d) =
4E_n/(d(E_n + 3))`, and the `log d` terms cancel (`m + 1 − (m + 1) = 0`). ∎

**Lemma 8.5 (exact step).** From `a = W_n(q)`, with `ℓ` as in Lemma 8.3, the point
`x = W_{n+1}(F_{n+1}(f_n(q) + ηS))` is an exact (`0`-approximate) mirror descent step on `K_m`.
*Proof.* Lemma 8.3 with `f_{n+1}(q') = f_n(q) + ηS`: the residual vanishes, so by Lemma 8.2
`φ(b) − φ(x) = D(b, x) ≥ 0` for every `b ∈ K_m`. ∎

**Lemma 8.6 (one-dimensional conjugate bound).** For `s ≥ 0`, `c > 0`, `r ∈ ℝ`:
`r(s − c) + δ(s, c) ≥ −c h(r)`. Moreover `0 ≤ h(r) ≤ e^{|r|}`.
*Proof.* `r(s − c) + δ(s, c) + c h(r) = s log(s/(c e^{−r})) − s + c e^{−r} = δ(s, c e^{−r}) ≥ 0`
(for `s = 0` both sides are `c e^{−r} ≥ 0`). `h(r) ≤ r ≤ e^r` for `r ≥ 0`;
`h(r) ≤ e^{−r} = e^{|r|}` for `r < 0`; `h ≥ 0` by convexity of `exp`. ∎

**Lemma 48 (frozen step; replaces the paper's Lemma 48).** From `a = W_n(q)`, with `ℓ` as in
Lemma 8.3, the point `x = W_{n+1}(q)` is a `q·h(r)`-approximate step, where
`r = m log(x_{n+1}(q)/x_n(q)) − ηS`; and `q h(r) ≤ q e^{η(m + |S|)}`.
*Proof.* Lemma 8.3 with `q' = q`: `f_{n+1}(q) − f_n(q) = m log(x_{n+1}(q)/x_n(q))` (the `q` and
`z` terms are unchanged), so `φ(b) − φ(x) = r (b(Q) − q) + D(b, x) ≥ r(b(Q) − q) + δ(b(Q), q)
≥ −q h(r)` (Lemma 8.2, dropping all `δ` terms but the `Q` one; Lemma 8.6). The last bound:
`|r| ≤ ηm + η|S|` by Lemma 8.1, then Lemma 8.6. ∎

**Lemma 8.7 (the trajectory is valid; Theorem 8, item 1).** For every loss sequence with the
constant coordinates of Lemma 8.3: `q_n ∈ (0, 2/d)`, `a 0 = u`, `a n ∈ K_m` positive, and
`a (n+1)` is an ε-approximate step from `a n` for `ℓ n`, for every `n`. `a n` is a measurable
function of `ℓ 0, …, ℓ (n−1)`.
*Proof.* Induction on `n`; frozen steps are ε-approximate by Lemma 48 and the switch
condition, exact steps by Lemma 8.5; measurability: `f_n`, `F_n` (monotone), `h`, `exp`, `log`
are measurable and the switch is a measurable set. No hypothesis on `η, ε` is used. ∎

### 3.4 The exact phase

Let `G_n := Σ_{s<n} S_s`.

**Lemma 8.8 (phase 1 is FTRL; cf. Lemma 10).** For `n ≤ τ`, `q_n = F_n(η G_n)`.
*Proof.* Induction: `q_0 = 1/d = F_0(0)` (Lemma 8.4); for `n < τ` the step is exact, so
`q_{n+1} = F_{n+1}(f_n(F_n(ηG_n)) + ηS_n) = F_{n+1}(ηG_{n+1})`. ∎
(This is Lemma 10 for this instance, with the corrected index range `L_{[0, n)}`.)

**Lemma 46 (first coordinates are high).** For all `n`, `q`: `x_n(q) ≥ ρ_n/d`; `ρ_n` is
increasing in `n`; `ρ_τ ≥ 3e³/(e³ + 3) ≥ 60/23 > 2.6`; hence `2/ρ_τ ≤ 23/30 ≤ e^{−1/4}`.
*Proof.* Lemma 8.1; `ητ ≥ 3` and `e³ ≥ 20`; `e^{−1/4} ≥ 1 − 1/4 + 1/32 − 1/384 > 0.778 >
23/30`. ∎ (The paper's `w_τ^i ≥ 5/(2d)`: `ρ_τ/d > 2.6/d`.)

**Lemma 47 (stuck base, sharpened).** For all `n ∈ ℕ`, `γ ∈ ℝ`:
`F_n(γ) ≤ (2/d)(2/ρ_n)^m e^γ`. Consequently, on `{G_τ ≤ τμ}` (with `ηd ≤ 1`, `ε ≤ 1/2`):
`q_τ ≤ (2/d)(2/ρ_τ)^m e^{ητμ} ≤ (2e^{3.02}/d) ε⁴ ≤ (41/d) ε⁴`.
*Proof.* Let `q = F_n(γ)`. Since `x_n(q) ≥ ρ_n/d` and `2/d − q ≤ 2/d`,
`γ = f_n(q) ≥ m log(ρ_n/d) + log q − (m+1) log(2/d)`, i.e.
`log q ≤ γ + m log(2/ρ_n) + log(2/d)`. For the consequence: Lemma 8.8, `ηG_τ ≤ ητμ ≤ ητ ≤
3.02`, `(2/ρ_τ)^m ≤ e^{−m/4} ≤ ε⁴` (Lemmas 46, 8.0a), `2e^{3.02} = 40.98…`. ∎

**Lemma 8.9 (phase 1 stays on the losing side).** If `ηn ≤ 4` and `m ≥ 7`, `μ ≤ 1`, then
`f_n(1/d) ≥ ηnμ`. Hence for `n ≤ τ`: on `{G_n ≤ nμ}`, `q_n ≤ 1/d`.
*Proof.* With `u = ηn`: `f_n(1/d) = m log(1 + 3(E_n − 1)/(E_n + 3))
≥ m·(3/4)(1 − e^{−u})` (from `log(1+x) ≥ x/(1+x)`) `≥ m·(3/4)·u/(1+u) ≥ (3m/20) u ≥ u ≥ uμ`.
Then `ηG_n ≤ ηnμ ≤ f_n(1/d)` and `F_n` is increasing: `q_n = F_n(ηG_n) ≤ 1/d`; `ηn ≤ ητ ≤ 4`
by Lemma 8.0c. ∎

### 3.5 The frozen phase

**Lemma 48' (stuck step; 8-G).** Assume `ηd ≤ 1`, `ε ≤ 1/2`, `εT ≤ 1` and `τ < T`. For
`τ ≤ n ≤ T` let `H_n := {G_τ ≤ τμ} ∩ ⋂_{τ ≤ s < n} {|S_s| ≤ 2L/η}`. On `H_n`: `q_n = q_τ ≤
(41/d)ε⁴ < 1/d`.
*Proof.* Induction on `n`. At `s ∈ [τ, n)`, `q_s = q_τ` and by Lemma 48
`q_s h(r_s) ≤ q_τ e^{ηm} e^{η|S_s|} ≤ (41/d) ε⁴ e^{1/5} e^{2L} = (41e^{1/5}/d) ε² ≤ (51/d) ε²
≤ ε`, since `51 ε ≤ 25.5 ≤ d`; so the step is frozen and `q_{s+1} = q_s`. Finally
`41 ε⁴ < 1` since `ε < 1/186` (Lemma 8.0e). ∎

### 3.6 Probabilities (8-G)

**Lemma 45 (hardness event; replaces the paper's Lemma 45).** Under the law `ν^G`, i.i.d. over
rounds, with `ηd ≤ 1`, `0 < ε ≤ 1/2`, `εT ≤ 1`:
(a) for every `n`, `P(G_n ≤ nμ) ≥ 1/2`;
(b) for every `s`, `P(|S_s| > 2L/η) ≤ ε/4`;
(c) for `τ ≤ n ≤ T`, `P(H_n) ≥ 1/2 − Tε/4 ≥ 1/4`.
*Proof.* (a) `G_n − nμ` is a sum of independent centred Gaussians (`n(m+1)` of them), so its
law is symmetric: `P(G_n − nμ ≤ 0) = P(G_n − nμ ≥ 0)`, and the two sum to at least `1`
(`n = 0`: `G_0 = 0`). (b) `S_s ~ N(μ, m+1)`, so `P(|S_s − μ| ≥ θ) ≤ 2exp(−θ²/(2(m+1)))`. Take
`θ = 2L/η − μ ≥ 2Ld − 1 ≥ Ld` (since `Ld ≥ 62 log 2 > 1`); with `2(m+1) ≤ d`:
`θ²/(2(m+1)) ≥ L²d ≥ (62 log 2) L ≥ L + log 8` (as `L ≥ log 2`); so the probability is
`≤ 2e^{−L}/8 = ε/4`. (c) Union bound: `P(H_n) ≥ P(G_τ ≤ τμ) − Σ_{τ≤s<n} P(|S_s| > 2L/η)`. ∎

### 3.7 Regret

**Lemma 8.10 (regret identity).** For a loss sequence with the constant coordinates of
Lemma 8.3: `⟨ℓ t, w*⟩ = 0` and `⟨ℓ t, a t⟩ = 3m y_t(q_t) + S_t z(q_t)`; hence
`regret ℓ a w* T = Σ_{t<T} (3m y_t(q_t) + S_t (2/d − q_t))`. Under `ν^G` (i.i.d.),
`E[regret] = Σ_{t<T} (3m E[y_t(q_t)] + μ E[2/d − q_t])`.
*Proof.* Lemma 44 and the coordinates of `W_t`. For the expectation: `q_t` is a bounded
measurable function of `ℓ 0, …, ℓ (t−1)`, independent of `S_t` (integrable, mean `μ`), so
`E[S_t (2/d − q_t)] = μ E[2/d − q_t]`; everything is integrable (`|S_t (2/d − q_t)| ≤ 2|S_t|/d`).
∎ (This replaces the paper's computation on the event `E`.)

**Theorem 49 (final bound; Theorem 8-G, item 2).**
(a) For every `t < T`, `P(q_t ≤ 1/d) ≥ 1/4`, hence `E[2/d − q_t] ≥ 1/(4d)` and
`μ Σ_{t<T} E[2/d − q_t] ≥ Tμ/(4d) = (1/4) T √(η/d)`.
(b) If `ηT ≥ 1`: `Σ_{t<T} 3m y_t(q_t) ≥ 3m/(2dη) ≥ D_R(w*, u)/(6η)` pointwise.
*Proof.* (a) `t ≤ τ`: Lemmas 8.9, 45a (`≥ 1/2`). `τ < t < T`: Lemmas 48', 45c (`≥ 1/4`). And
`2/d − q_t ≥ 1/d` on `{q_t ≤ 1/d}`, `> 0` always. (b) `q_t > 0` gives
`y_t(q_t) ≥ (3/d)/(E_t + 3)`; for `ηt ≤ 1`, `E_t + 3 ≤ e + 3 ≤ 6`, so `y_t ≥ 1/(2d)`; there are
`min(T, ⌊1/η⌋ + 1) ≥ 1/η` rounds `t < T` with `ηt ≤ 1`. `D_R(w*, u) = (5m log 5 + 2 log 2)/d ≤
9m/d` (`5 log 5 < 8.05`, `m ≥ 2`), so `3m/(2dη) = (9m/d)/(6η) ≥ D_R(w*, u)/(6η)`. Sum with
Lemma 8.10 (both parts are nonnegative). ∎

**Corollary (paper's form; item 3).** Lemma 8.0d: `√d ≤ 10√L`. ∎

### 3.8 What each hypothesis is used for (8-G)

- `ε ≤ 1/2`: Lemma 8.0 (`m ≥ 12`, `d ≥ 62`, `d ≤ 100L`), Lemmas 8.9, 48', 45b, 49b.
- `ηd ≤ 1`: `μ ≤ 1` (Lemmas 8.9, 47, 45b), `ηm < 1/5` (48'), `ητ ≤ 3.02` (47, 8.9).
- `εT ≤ 1`: Lemma 45c (union bound) and Lemma 8.0e (`q_τ < 1/d`).
- `ηT ≥ 1`: Theorem 49b only.

### 3.9 Variant deltas

- **8-B** (`ε ≤ 1/3`, so `m ≥ 18`, `d ≥ 92`; no `εT ≤ 1`): Lemma 45a holds (sum of independent
  symmetric variables, `S − μ = Σ_i ℓ(Z i)`); instead of 45b, `|S_s| ≤ m + 1` surely, so
  `|r_s| ≤ η(2m + 1) ≤ 37/92 < 0.41` and Lemma 48' holds on `{G_τ ≤ τμ}` for **all** `n ≥ τ`:
  `q_τ e^{0.41} ≤ (41·1.51/d) ε⁴ ≤ (62/d) ε⁴ ≤ ε`, and `q_τ ≤ (41/81)/d < 1/d`. So
  `P(q_t ≤ 1/d) ≥ 1/2` for every `t`: constant `1/2`, and `1/20` in the paper's form.
- **8-C** (`ε ≤ 1/3`, no `εT ≤ 1`): `G_n = nμ` surely; Lemma 8.9 gives `q_n ≤ 1/d` for
  `n ≤ τ`; `|r_s| ≤ η(m + μ) ≤ 0.211`, Lemma 48' holds for all `n ≥ τ` surely
  (`(41e^{0.211}/d) ε⁴ ≤ (51/d) ε⁴ ≤ ε`). So `q_t ≤ 1/d` for every `t` and
  `regret ≥ Tμ/d = T√(η/d)` (`1/10` in the paper's form). Lemma 8.10 without expectation.

### 3.10 Lean dependencies

`Real.exp`/`log` inequalities (`log(1+x) ≥ x/(1+x)`, `e³ ≥ 20`, `e^{3.02} ≤ 20.5`,
`e^{1/5} ≤ 1.222`, `e^{0.41} ≤ 1.51`, alternating-series bounds for `e^{−1/4}`); a strictly
monotone continuous bijection `(0, 2/d) → ℝ` and its inverse (`StrictMonoOn`, IVT,
`Monotone.measurable`); `negEntropy`, `bregDiv`; for 8-G: product measures, sums of independent
Gaussians (`gaussianReal` convolution), the Gaussian tail bound (mgf/Chernoff), symmetry;
`iIndepFun` and `IndepFun` of a function of the past and the present loss; integrability.

## 4. Errata (area D)

Locations refer to v2. Kinds: typo / wrong constant / missing hypothesis / gap in the proof /
false statement. Numbered `D1, …` here; the errata file assigns the final `E` numbers.

- **D1.** Theorem 8 (main text): quantifier order. "There exists a polytope `K ⊆ Δ_d` and a
  distribution … such that for any `ε > 0` …": the construction's `K` depends on `ε`
  (`m = 16 log(1/ε)`, `d = 5m + 2`) and the law on `ε` and `η` (mean `√(ηd)`); the proof also
  constrains `T` (`m ≥ 128 log(2T)`). Correction: `∀ η, ε` in range, `∃ K_ε`, law`_{ε,η}`, trajectory,
  `w`, `∀ T` in range. Also the dimension must be part of the statement (`d ≤ 100 log(1/ε)`):
  without it the statement follows trivially from Theorem 35 in dimension `d ≥ η²e^η/ε`.
  Kind: false statement (as written) / imprecise.
- **D2.** Theorem 8: "for any `ε > 0`". Meaningless for `ε ≥ 1` (`log(1/ε) ≤ 0`); as `ε → 1`
  the bound exceeds `2T` (the maximal regret for losses in `[−1,1]^d`). The proof needs
  `d ≤ 1/η` (D3), `m ≥ 128 log 2T` (i.e. `ε ≤ (2T)^{−8}`) and `ε < 4η`; the remark "obviously
  proof that works for small ε works for bigger" gives, for a larger `ε`, the bound with the
  smaller `log(1/ε₀)`, not with `log(1/ε)`. Correction: Theorem 8-G's ranges `ε ≤ 1/2`,
  `εT ≤ 1`, `100η log(1/ε) ≤ 1` (8-B/8-C: `ε ≤ 1/3`, `100η log(1/ε) ≤ 1`). Kind: missing
  hypothesis.
- **D3.** Appendix, "General settings and hardness event": "there's a known lower bound for
  `Tη`, we can assume `d ≤ 1/η`" — no such bound is proved or cited; the regime `ηd > 1`
  (`ε ≲ e^{−1/(100η)}`) is not covered. Correction: hypothesis `ηd ≤ 1`. Also affects the
  claim "Ω̃(T^{2/3}) for any step size" (Section 4.2) for large step sizes. Kind: missing
  hypothesis.
- **D4.** Appendix, "Polytope definition": `m = 16 log(1/ε)` and `τ = 3/η` are not integers.
  Correction: `m = ⌈16 log(1/ε)⌉`, `τ = ⌈3/η⌉`; then `e^{−m/16} ≤ ε` (instead of `= ε`, used in
  Lemma 48) and `3 ≤ ητ < 3 + η`. Kind: typo.
- **D5.** Lemma 43, proof: "A is already in echelon form" — it is not (rows `A_i` and `A_{m+i}`
  have the same leading column); `A` has full rank `4m + 1` nevertheless (each row group has a
  private coordinate after eliminating `A_{m+i}`). Kind: typo (claim true).
- **D6.** Lemma 45 (`P(E) = Ω(1)`), proof. (a) `μ = √(dη)τ = 2√(d/η)` and `σ² = 2(m+1)/η`:
  with `τ = 3/η` these are `3√(d/η)` and `3(m+1)/η` (typo). (b) `P(G ≤ 0) = Φ(−√(3d/(m+1)))`
  (for `ητ = 3`), between `5·10⁻⁵` and `9.2·10⁻⁵` for `m ≥ 8` — a constant, but tiny. (c) "Using Hoeffding
  inequality we have that w.p. `1/(2T)`: `Σ ℓ_t(i) ≤ √((m+1)/2 · log 2T)`": Hoeffding does not
  apply to Gaussians; the sum has mean `√(ηd) ≠ 0`; for `N(·, 1)` variables the deviation at
  level `1/(2T)` is `√(2(m+1) log 2T)` (twice the paper's); "w.p. `1/(2T)`" should be "except
  with probability `1/(2T)`". Numerically `P(S_t > √((m+1)/2 · log 2T)) ≈ 0.064` for
  `m = 896, T = 64`, against the claimed `1/(2T) = 0.0078`. (d) The union bound controls the
  second part of `E` only up to probability `1/2`, and `P(G ≤ 0) < 1/2`, so `P(E) = Ω(1)` does
  not follow; independence is not available either, since the second part also constrains the
  rounds `t < τ` that make up `G`. Correction: Lemma 45 (Section 3.6) with the event
  `{G_τ ≤ E G_τ} ∩ {|S_s| ≤ 2 log(1/ε)/η, τ ≤ s < T}`, `P ≥ 1/4` under `εT ≤ 1`, using the
  sharpened Lemma 47 (which tolerates `ηG_τ ≤ 3.02`). Kind: gap in the proof; wrong constant.
- **D7.** Lemma 46, proof: "Assume by contradiction that `w_τ^i ≥ 3/d`" should be "suppose
  `w_τ^i < 3/d` (otherwise there is nothing to prove)"; "`w_t^{m+i} = w_t^{2m+i} = w_t^{m+i}`"
  should end with `w_t^{3m+i}`; Lemma 10 is applied with `ℓ_{:τ}` (`τ` losses) to `w_τ`, which
  is after `τ − 1` steps (see D12). The statement is true; in fact `w_τ^i = e^{η(τ−1)}
  w_τ^{m+i}` exactly, which gives `w_τ^i ≥ 3e^{η(τ−1)}/((e^{η(τ−1)} + 3)d)`. Kind: typo.
- **D8.** Lemma 47. Statement: "`α_τ^{m+1} ≤ −1/d + e^{m/8}`" should be `e^{−m/8}` (as used in
  Lemma 48 and Theorem 49). Proof: the bounds are inverted: "`w_τ^i ≤ 1/(2d)` for
  `i ∈ [4m+1, 5m+1]`" is false (`α_τ^{m+1} ∈ [−1/d, 0]` gives `w_τ^i ∈ [1/d, 2/d]`; numerically
  `d w_τ^i ∈ [1.89, 2]`); "`w_1^i/w_τ^i ≥ 2`" should be `≥ 1/2`; "`w_1^i/w_τ^i ≤ 2.5`" (first
  coordinates, from Lemma 46) should be `≤ 1/2.5`; the displayed inequality should read
  `log(w_1^{5m+2}/w_τ^{5m+2}) ≥ m log 2.5 − (m + 1) log 2`; then `(m+1) log 2 ≤ m log 2.2`
  (true for `m ≥ 7.28`) and `log(2.5/2.2) = 0.1278 ≥ 1/8` give `w_τ^{5m+2} ≤ e^{−m/8}/d`. As
  written, the derivation yields the useless `w_τ^{5m+2} ≤ e^{m/8}`. Corrected and sharpened:
  Lemma 47 (Section 3.4), which needs only `ηG_τ ≤ 3.02` instead of `G_τ ≤ 0`. Kind: typo
  (signs); the corrected argument works.
- **D9.** Lemma 48, proof. (a) "`⟨ℓ_t, v_i⟩` has a constant value of `−1`": it is `−3`.
  (b) The argument that the exact step has `α_t^i ≥ α_{t−1}^i`: from `w_t^i ≤ w_{t−1}^i + ε` it
  writes `3 log((w_t^i − ε)/w_t^i)` and concludes `−η ≥ log(1 − ε/4) ≥ −ε/4`; the `1 − ε/4` has
  no source (it would need `w_t^i ≥ 4`), and `log(1 − x) ≥ −x` is false (`log(1−x) ≤ −x`), so
  `ε ≥ 4η` does not follow. The claim is true in the corrected regime but unproved;
  numerically it fails outside it (`m = 3, η = 0.05 > 1/d`). (c) It uses `S_t ≤ m/16` from `E`
  (see D6). (d) Membership in `K` and positivity of the modified point are not checked (they
  hold). (e) "`w_t^{5m+2} ≤ w_{t−1}^{5m+2} e^{m/16}`" drops the factor `η` (harmless).
  Correction: the explicit frozen step `W_{n+1}(q_n)` with the closed-form suboptimality bound
  `q_n h(r_n)` (Lemma 48, Section 3.3); no comparison with the exact step. Kind: gap in the
  proof.
- **D10.** Theorem 49, proof. (a) "The total expected loss of this coordinate is `T√(dη)`" is
  computed on `E`, but `E` depends on the losses of the same rounds (`{G ≤ 0}` biases the
  `Z`- and `P`-losses of rounds `< τ` downward, `{S_t ≤ m/16}` those of round `t`); the
  trajectory is not defined off `E`, whose contribution is ignored. Correct argument:
  predictability gives `E⟨ℓ_t, w_t⟩ = 3m E[y_t] + √(ηd) E[z_t]` exactly (Lemma 8.10), and
  `E[z_t] ≥ P(z_t ≥ 1/d)/d`. (b) Only rounds `t ≥ τ` are counted, which needs `T ≥ 2τ` (not
  assumed); with the median event every round counts. (c) "all coordinates with non-zero loss
  (`[m+1, 4m]`, `5m+1`) are zeroed": the `Z`-coordinates `[4m+1, 5m]` also have nonzero loss;
  they are zeroed too (`w^{4m+i} = w^{5m+1}` on `K`), so the comparator has zero loss. Kind: gap
  in the proof (a, b); typo (c).
- **D11.** Theorem 8: the term `D_R(w, w₁)/η` is not proved anywhere (Theorem 49 only gives
  `T√(η/log(1/ε))`). It holds for `w = w*` when `ηT ≥ 1` (Theorem 49b: the `Y`-coordinates,
  with deterministic loss `1`, give `Σ_t 3m y_t ≥ 3m/(2dη) ≥ D_R(w*, w₁)/(6η)`), and fails for
  `ηT < 0.26` (regret `≤ T`, `D_R(w*, w₁)/(6η) ≥ 0.26/η`). Correction: add `ηT ≥ 1` for this
  term. Kind: gap in the proof; missing hypothesis.
- **D12.** Lemma 10 (already noted): `B^v(t₁, t₂) = η⟨ℓ_{t₁:t₂−1}, v⟩`, not `ℓ_{t₁:t₂}`; the
  proof sums over `t' ∈ [t₁, t₂]` instead of `[t₁ + 1, t₂]`. Lean: `B(s, t) = η⟨L_{[s,t)}, v⟩`.
  The corrected proof of Theorem 8 does not use Lemma 10 (Lemma 8.8 is its instance). Kind:
  typo.
- **D13.** The losses are Gaussian, hence unbounded, outside the standing assumption
  `‖ℓ_t‖_* ≤ 1` (Section 2) and the class `[−1, 1]^d` of Theorem 7, which Theorem 8 is meant to
  contrast with. Not an error of Theorem 8's statement ("a distribution of losses"); bounded
  (8-B) or constant (8-C) losses work with the same proof. The noise is not needed at all:
  only the paper's crude Lemma 47 (which needs `G ≤ 0`) requires it. Kind: imprecision.
- **D14.** "Assume … `ε < 4η`": not needed (it only serves the flawed step D9b). In the corrected
  8-G, `τ < T` and `εT ≤ 1` give `ε < η/3` anyway. Kind: remark (unneeded hypothesis).

## 5. Numerical checks

All scripts in
`/tmp/claude-663481/-home-rdegenne-Documents-Lean-Schlisselberg2026Hidden/7ad2edfa-b559-4fea-932a-1aff1e8cf05b/scratchpad/polytope-lower/`,
run with `python3 -I <script>`.

- `check_polytope.py` (`m = 1, 2, 3, 8, 12, 20`): `rank A = 4m + 1`, `A v_j = 0`,
  `ker A = span(v_1, …, v_{m+1})`, column sums of `V` are `0`; Lemma 43's coordinate
  description on random points of `K`; `w* ∈ K`, `A w* = b`, its support has zero loss;
  `D_R(w*, u) = (5m log 5 + 2 log 2)/d` (`1.58` for `m = 12`), and `≤ 9m/d` for `m ≥ 2` (fails
  at `m = 1`, irrelevant).
- `check_steps.py` (mpmath, 60 digits): exact OMD steps computed by a generic damped Newton
  method on the kernel coordinates (no symmetry assumed, random asymmetric `Z`-losses) agree
  with the closed form `W_{n+1}(F_{n+1}(f_n(q) + ηS))` to `≤ 2·10⁻³⁶`, and the closed form's
  suboptimality is `≤ 10⁻⁶¹` (18 cases, `m ∈ {3, 4, 8, 12}`, states from uniform to
  `q d = 10⁻⁵`, `S` up to `38`). The frozen point's true suboptimality is always `≤ q h(r)`,
  with ratio up to `0.9999` (the bound is tight when `q` is small). One case (`m = 3`,
  `η = 0.05 > 1/d`) has `β` increasing and `α^i` decreasing: the paper's Lemma 48 claim fails
  outside the regime.
- `check_identities.py` (mpmath): Lemma 8.2 + 8.3 identity on 60 random `(a, x, b, ℓ)`,
  including `b` on the boundary of `K`, error `≤ 10⁻⁴⁹`; Lemma 47 on 200 random `(n, γ)`
  (`m ∈ {8, 12, 30, 100}`, `γ ∈ [−50, 50]`): no violation, and nearly tight (to 10 digits) for
  large `ηn`; Lemma 8.9: `min (f_n(1/d) − ηn) = 0.04 > 0` over `m ≥ 12`, `ηn ∈ (0, 4]`;
  `h(r) ≤ e^{|r|}`; `0 ≤ log(x_{n+1}/x_n) ≤ η`.
- `check_paper_lemmas.py`: `ρ(3) = 2.6101`, `16 log(ρ(3)/2) = 4.26`; the paper's Lemma 47 at
  `G_τ = 0` (the worst case of `{G_τ ≤ 0}`): `d z_τ ∈ [1.89, 2]` (paper: `≤ 1/2`),
  `d q_τ ≤ e^{−m/8}` and `≤ 2(2/ρ_τ)^m`; `m log 1.25 − log 2 ≥ m/8` iff `m ≥ 7.06`;
  `P(G_τ ≤ 0) = 9.1·10⁻⁵` (`m = 8`), `7.8·10⁻⁵` (`m = 12`), `5.6·10⁻⁵` (`m = 129`),
  `5.4·10⁻⁵` (`m = 10⁴`), with `E G = 3√(d/η)`, `Var G = 3(m+1)/η`; the paper's per-round
  threshold fails (`P ≈ 0.064` vs `1/(2T) = 0.0078`, union over `T` rounds `4.08`);
  `P(|S| > 2L/η) ≤ 10⁻¹²⁸ ≪ ε/4` for `ε ∈ {1/2, 1/186, 1/3000}`.
- `simulate.py` (8-G, Monte Carlo, 200–400 runs, all hypotheses: `T = 3000, ε = 1/3000,
  m = 129, d = 647, η = 1/d`; `T = 20000, ε = 1/20000, m = 159, d = 797, η ∈ {1/d, 1/(3d)}`):
  never unfrozen in phase 2, largest certified suboptimality used `2·10⁻¹⁸ ≪ ε`,
  `min_t P(q_t ≤ 1/d) = 1.000`, `E[Regret]` (`604`, `796`, `2266`) above the bound (`174`,
  `220`, `644`). At these horizons the exact trajectory has the same regret: it does not leave
  the losing side before `T`.
- `semi_analytic.py` (8-G, Gauss–Hermite quadrature over `G_t`, horizons up to `10⁸`, `ε = 1/T`,
  `η = 1/d`): exact vs frozen expected regret: `T = 10⁶`: `1769` vs `2840` (bound `523`);
  `T = 10⁷`: `2078` vs `16690` (bound `2281`, above the exact trajectory's regret);
  `T = 10⁸`: `2376` vs `136793` (bound `17322`). The exact trajectory leaves the losing side at
  `t ≈ 0.28 √d η^{−3/2}`; beyond that the bound is a genuine cost of approximation, and the
  frozen regret is close to `2T√(η/d)` (8 times the proved constant `1/4`).
- `simulate_bounded.py` (8-B with `P`-loss `μ + (1 − μ)·Rademacher` instead of `δ_μ`, also in
  `[−1, 1]` and with `|S| ≤ m + 1`; 1000 runs, `T = 20000`, `ε ∈ {1/3, 1/10}`,
  `η ∈ {1/d, 1/(4d)}`, no condition on `T`): empirical `P(G_τ ≤ τμ) ∈ [0.47, 0.50]` (sampling
  error `±0.016`; the true value is `≥ 1/2` by symmetry), never unfrozen
  (`|r| ≤ 0.31 < η(2m+1)`), `min_t P(q_t ≤ 1/d) ≥ 0.999`, `E[Regret]` (`502`, `556`, `389`,
  `806`) above the bound `D_R/(6η) + T√(η/d)/2` (`133`, `152`, `103`, `226`).
- `simulate_deterministic.py` (8-C, constant losses, mpmath 60 digits, `T = 12000`,
  `ε ∈ {1/3, 1/10}`, `η = 1/d`): never unfrozen after `τ`; at rounds `τ − 1, τ, τ + 1, 5000,
  11999` the true suboptimality of the frozen point (against the closed-form exact minimizer)
  is `0.42`–`0.94` times the certificate `q h(r)`, which is at most `10⁻⁷ ≪ ε`; `d q_τ = 0.086`
  (`ε = 1/3`) and `0.0020` (`ε = 1/10`). Regret: `ε = 1/3` (`m = 18`, `d = 92`): frozen `335.9`,
  exact `146.4` (leaves the losing side at `n = 2296`), bound `D_R/(6η) + T√(η/d) = 154.8` —
  the exact trajectory is below the bound, the frozen one above; `ε = 1/10` (`m = 37`,
  `d = 187`): frozen `303.1`, exact `268.0` (leaves at `n = 9592`), bound `114.0`.

## 6. Open points and decisions for the user

- **Which law** (decision): 8-G keeps the paper's Gaussian law but needs `εT ≤ 1`, Gaussian
  sums and tails, and gives `1/4`; 8-B (Rademacher, losses in `[−1, 1]^d` like Theorem 7) needs
  no condition on `T` and only symmetry, constant `1/2`; 8-C (constant losses) needs no
  probability at all, constant `1`, and proves the paper's existential claim with a Dirac law.
  Recommendation: 8-C as the headline (or 8-B if a non-degenerate i.i.d. law is wanted), with
  8-G optional.
- The median event `{G_τ ≤ E G_τ}` and the frozen step are deviations from the paper's proof
  (D6, D8, D9), not from its statement.
- For moderate `T` the exact trajectory may also satisfy the bound (8-G with `ε = 1/T`: up to
  `T ≈ 10⁶`); the lower bound separates exact from approximate OMD only once the exact
  trajectory leaves the losing side, at `t ≈ 0.28 √d η^{−3/2}` (e.g. `T = 12000` suffices for
  8-C with `ε = 1/3`, `η = 1/d`). Not an error, but the paper's word "excess" is only justified
  in that regime.
- `ηd > 1` (D3) stays open: not proved, and not needed for the `Ω̃(T^{2/3})` discussion at the
  optimal `η ≈ (log(1/ε))^{1/3} T^{−2/3}`, which satisfies `ηd ≤ 1` for large `T`.
