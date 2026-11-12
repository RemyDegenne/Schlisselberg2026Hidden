# Modelling decisions

How the objects of [SSKM26] (arXiv:2511.22283v2, `source/arXiv-2511.22283v2/main.tex`) are
represented in Lean. The statements of the headline results follow these conventions; deviations
from the paper that are not generalizations are entries of `notes/paper-errata.md`.

Decided with the user on 2026-11-12:
- headline results: Theorems 2–8, Lemmas 14–15, Theorems 35, 36, 52;
- **explicit constants** everywhere: every `O(·)`, `Ω(·)` of the paper becomes an explicit
  numerical constant, and every threshold the paper's proof does not support is replaced by a
  corrected explicit one, with an erratum entry;
- Theorem 5 is stated for losses in `[0, 1]^d`, keeping the threshold `e^{-ηT/2}` (it is false for
  losses in `[-1, 1]^d`, erratum).

## Rounds and indices

Lean rounds are numbered from `0`, as in LMLExplore's online-learning files:
- the paper's `w_t` is `a (t - 1)`: `a 0` is the initial point `w_1`;
- the paper's horizon `T` is the Lean horizon `T`: rounds `0, …, T - 1`;
- the step of round `t < T` takes `a t` and the loss `ℓ t` to `a (t + 1)`;
- the regret against `u` is `regret ℓ a u T = ∑ t < T, (⟨ℓ t, a t⟩ - ⟨ℓ t, u⟩)` (LMLExplore's
  `LMLExplore.OnlineLearning.regret`), which uses `a 0, …, a (T - 1)`;
- the paper's cumulative loss `ℓ_{t₁:t₂}` (inclusive) is a sum over a half-open interval of Lean
  rounds, `L_{[s, t)} = ∑ s ≤ r < t, ℓ r`, written with `Finset.Ico s t`.

## Inexact mirror descent steps

`x` is an **ε-approximate mirror descent step** on `K` from `a`, with potential `F`, derivative
`F'` of `F` at `a`, learning rate `η` and linear loss `y`, if `x ∈ K` and for every `b ∈ K`,
`η y x + D_F(x, a) ≤ η y b + D_F(b, a) + ε`, where `D_F(b, a) = F b - F a - F' (b - a)` is LML's
`bregDiv F b a F'`. For `ε = 0` this is LMLExplore's `IsMirrorDescentStep`. This is the paper's
definition (`φ_t(w_{t+1}) ≤ min_K φ_t + ε`) without assuming that the minimum is attained.

An **ε-approximate trajectory** for `T` rounds is a sequence `a` with `a 0 ∈ K` and, for every
`t < T`, `a (t + 1)` an ε-approximate step from `a t` for the loss of round `t`.

**Derivatives.** The objective of round `t` needs `∇R(w_t)`. The general statements (Theorems 2,
52) work in a real normed space `E`, with losses `y t : E →L[ℝ] ℝ` (the dual norm is the operator
norm) and a derivative of `R` within `K` at every point of `K`. The statements on the simplex and
its subsets work on `α → ℝ` for a finite type `α` (`d = Fintype.card α`, never `Fin d`), with:
- the coordinate-separable regularizer `R w = ∑ i, r (w i)` for `r : ℝ → ℝ`;
- its gradient at `w` used in the steps, `h ↦ ∑ i, deriv r (w i) * h i`;
- the hypothesis that every iterate has positive coordinates. The paper assumes it implicitly:
  `∇R(w_t)` does not exist at a point with a zero coordinate, for every ν-barrier. Upper bounds
  assume it of the trajectory; lower bounds construct positive trajectories.
- losses `ℓ t : α → ℝ` with `⟨ℓ, w⟩ = ∑ i, ℓ i * w i`; "losses in `[0, 1]^d`" is
  `∀ t i, ℓ t i ∈ Set.Icc 0 1`.

The norm: the paper's simplex results use the `ℓ¹` norm and its dual sup norm. Statements that need
a norm (strong convexity, dual norms of the losses) on the simplex use the coordinates directly
(`∑ i, |h i|`, `|ℓ t i| ≤ 1`), or `PiLp 1`, as LMLExplore's `negEntropy` files do.

## Regularizers

- **ν-barrier** (Definition 1): `r : ℝ → ℝ` twice differentiable on `(0, 1)` with
  `c₁ / x ^ ν ≤ r'' x ≤ c₂ / x ^ ν` for `x ∈ (0, 1)`, for some `ν ≥ 1` and `0 < c₁, c₂`. The paper
  asks this on `(0, 1]` for a function on `[0, 1]`; the iterates of a trajectory on the simplex of
  dimension `d ≥ 2` with positive coordinates have coordinates in `(0, 1)`, and so do the segments
  between them. `r''` is not assumed monotone (Definition 1 does not assume it; Definition 18,
  which does, is not used).
- **Negative entropy**: LMLExplore's `negEntropy w = ∑ i, (w i * log (w i) - w i)`, whose Bregman
  divergence on the simplex is the paper's (`r(x) = x log x`, `ν = 1`, `c₁ = c₂ = 1`): the two
  differ by the linear function `∑ i, w i`.
- **Smooth regularizers** (Theorems 2, 3): `R : E → ℝ` with a derivative `R' x` within `K` at
  every `x ∈ K` and `‖R' x - R' y‖ ≤ β ‖x - y‖` on `K`, 1-strongly convex on `K` for the norm of
  `E` (the paper's standing assumption, Section 2).

## Domains

- The simplex is LMLExplore's `simplex α`; the uniform distribution is `fun _ ↦ 1 / d`.
- A polytope in standard form is `K = {w | (∀ i, 0 ≤ w i) ∧ A w = b}` for a linear map `A` from
  `α → ℝ` to a real vector space; `ker A` is its direction. The paper's "polytope `K ⊆ Δ_d`
  containing the uniform distribution" is this with `K ⊆ simplex α` and the uniform point in `K`.

## Balance

- Balance of a trajectory (Definition 9) for `v ∈ ker A` and rounds `s ≤ t`:
  `B^v(s, t) = ⟨∇R(a s) - ∇R(a t), v⟩ = ∑ i, (r' (a s i) - r' (a t i)) * v i`.
- On the simplex, with a fixed coordinate `i*` minimizing the cumulative loss `L_{[0, T)}`, the
  losses are **α-balanced** if for all `s ≤ t ≤ T` and all `i`,
  `L^{i*}_{[s, t)} - L^{i}_{[s, t)} ≤ α`. This is the notion the proofs of Lemmas 13, 15 and 40
  use (Definition 32), which the paper also calls α-balanced; it differs by a factor `2` from the
  `ℓ¹` notion of Section 5.1 with `v = e_{i*} - e_i`. Lemmas 14 and 15 are stated with it.

## Random losses (Theorems 7, 8)

A probability space `(Ω, P)` and losses `ℓ : ℕ → Ω → α → ℝ`, measurable, independent and
identically distributed over the rounds (`iIndepFun`, `IdentDistrib`). Theorem 7 holds for every
trajectory, which may depend on the realization: there is a measurable event of probability at
least `1 - δ` on which every ε-approximate trajectory satisfies the bound. In Theorem 8 the
constructed trajectory is a function of the losses, each play depending on the past losses only.
