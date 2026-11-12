# Paper roadmap: The Hidden Cost of Approximation in Online Mirror Descent

Paper: RemyDegenne/Schlisselberg2026Hidden · LMLExplore 469c4c5710e0 · LMLRoadmaps 468f19f45fae · Refreshed 2026-11-12

## Items

| Id | Item | Tag | Link | Status | Files |
|---|---|---|---|---|---|
| R1 | Bregman divergence and the three-point identity | exists | `bregDiv_three_point` | – | |
| R2 | Exact mirror descent steps, their existence and regret bounds | exists | `LMLExplore.OnlineLearning.IsMirrorDescentStep` | – | |
| R3 | FTRL plays, their existence, the first-order condition at a minimizer and the be-the-leader lemma | exists | `LMLExplore.OnlineLearning.sum_le_of_isMinOn_sum` | – | |
| R4 | Regret against a fixed comparator | exists | `LMLExplore.OnlineLearning.regret` | – | |
| R5 | Bregman divergences of strongly convex functions and the stability bound of a step | exists | `LMLExplore.OnlineLearning.apply_sub_sub_div_le_of_mul_norm_sq_le` | – | |
| R6 | The simplex, the negative entropy, Pinsker's inequality and the Gibbs variational principle | exists | `LMLExplore.negEntropy` | – | |
| R7 | Hoeffding's inequality for independent bounded variables, and i.i.d. sequences as `Measure.infinitePi` | exists | `ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` | – | |
| R8 | The descent lemma: quadratic bounds for a function with a Lipschitz derivative on a convex set | target | OnlineLearning 1.3 | PR #301 | `ForLMLExplore/Analysis/Convex/Smooth.lean` |
| R9 | Multiplicative weights as the mirror descent step of the negative entropy on the simplex | target | OnlineLearning 6.2 | PR #302 | `ForLMLExplore/OnlineLearning/ExponentiatedGradient.lean` |
| R10 | Derivative and Bregman divergence of the negative entropy on `α → ℝ` | refactor | `LMLExplore.bregDiv_negEntropy` | PR #303 | `ForLMLExplore/Analysis/Convex/NegEntropy.lean` |
| R11 | Approximate mirror descent steps: definition and basic API | staged | S1 | proved | `ForLMLExplore/OnlineLearning/ApproxMirrorDescent.lean` |
| R12 | Regret of approximate mirror descent with a smooth regularizer, with the approximate first-order condition of an ε-minimizer | staged | S1 | proved | `ForLMLExplore/Analysis/Convex/ApproxMinimizer.lean`, `ForLMLExplore/OnlineLearning/ApproxMirrorDescent/Smooth.lean` |
| R13 | Approximate FTRL plays: definition, basic API and regret bound | staged | S1 | proved | `ForLMLExplore/OnlineLearning/FTRL/Approx.lean`, `ForLMLExplore/Analysis/Real/Sqrt.lean` |
| R14 | Power barriers and coordinate-separable regularizers: examples, scalar bounds, derivative, Bregman divergence, strong convexity | staged | S2 | todo | `ForLMLExplore/Analysis/Convex/PowerBarrier.lean` |
| R15 | Polytopes in standard form inside the simplex: convexity, feasible directions, ℓ¹ bounds on differences | staged | S3 | todo | `ForLMLExplore/Analysis/Convex/StandardFormPolytope.lean` |
| R16 | Stuck trajectories: the error of staying put, for the negative entropy and for power barriers | paper | | proved | `SSKM2026/Lemma34.lean` |
| R17 | Negative entropy on the simplex: step sizes, balance, lower bounds on the iterates, balance of i.i.d. losses | paper | | proved | `SSKM2026/EntropyUpper/Lemma13.lean`, `SSKM2026/EntropyUpper/Lemma21.lean`, `SSKM2026/EntropyUpper/Lemma22.lean`, `SSKM2026/EntropyUpper/Lemma24.lean`, `SSKM2026/EntropyUpper/Lemma33.lean`, `SSKM2026/EntropyUpper/Lemma39.lean`, `SSKM2026/EntropyUpper/Lemma40.lean`, `SSKM2026/EntropyUpper/IidBalanced.lean` |
| R18 | Power barriers on polytopes: balance, lower bound on the iterates, one-round inequality | paper | | todo | |
| R19 | The polytope, the losses and the trajectory of Theorem 8 | paper | | proved | `SSKM2026/Lemma44.lean`, `SSKM2026/Lemma48.lean`, `SSKM2026/Lemma47.lean`, `SSKM2026/Theorem49.lean` |

## Notes

- R1: LML's `bregDiv f x y J = f x - f y - J (x - y)`; the three-point identity is the paper's
  Lemma 26.
- R2: also `IsMirrorDescentStep.mul_apply_sub_le`, `exists_isMirrorDescentStep`,
  `mirrorDescent_regret_le_bregDiv_div` and `mirrorDescent_regret_le_of_strongConvexOn`.
- R3: also `IsFTRLPlay`, `exists_ftrl` and `bregDiv_le_sub_of_isMinOn`. The be-the-leader lemma
  is the paper's Lemma 50.
- R5: also `StrongConvexOn.mul_norm_sub_sq_le_bregDiv`. With `m = 1` the stability bound is the
  paper's Lemma 27.
- R6: also `simplex`, `uniform_mem_simplex`, `bregDiv_negEntropy`, `strongConvexOn_negEntropy`,
  `sq_sum_abs_sub_le_two_mul_sum_mul_log_div` (Pinsker), `softmax` and
  `isGreatest_sum_sub_mul_sub_sum_mul_log_div_div` (Gibbs).
- R7: also `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` (Hoeffding's
  lemma) and `ProbabilityTheory.iIndepFun_infinitePi`, all in Mathlib.
- R8: OnlineLearning 1.3 defines `s`-smoothness on a convex set `V` (differentiable on an open set
  containing `V`, with an `s`-Lipschitz derivative on `V` for the dual norm) and asks for the
  two-sided bound `|f y - f x - f' x (y - x)| ≤ s / 2 * ‖y - x‖ ^ 2` on `V`. The paper uses the
  upper bound with a derivative within `K` at every point of `K`. The file proves the two-sided
  bound under that weaker hypothesis (`Convex.abs_bregDiv_le_mul_norm_sub_sq`) and the target's
  form with its hypotheses written out (`Convex.abs_bregDiv_fderiv_le_mul_norm_sub_sq`); the port
  adds the target's definition and states that form with it. The other claims of 1.3 (gradient
  bound, self-bounded functions) are not needed here. PR #301 ports it as `LMLExplore.SmoothOn`,
  with `Convex.norm_bregDiv_le_mul_norm_sub_sq` (for `F`-valued functions, the local
  `Convex.abs_bregDiv_le_mul_norm_sub_sq` at `F = ℝ`) and `Convex.bregDiv_le_mul_norm_sub_sq`.
- R9: OnlineLearning 6.2 asks, on `simplex α`, that the mirror descent step with the negative
  entropy be the multiplicative update `x_{t+1} ∝ x_t e^{-η y_t}` and that its iterates stay
  positive. It also asks that from the uniform start with a constant rate the iterates be
  `softmax (-η ∑_{s ≤ t} y_s)`, and that adding a constant to a loss change no play. The paper uses
  the first claim from any point with positive coordinates, for any loss and any `η`, together
  with the minimum value `-log ∑ a, x a * exp (-η y a)` of the objective; both come from the Gibbs
  variational principle of R6. State the step with `IsMirrorDescentStep`, on `α → ℝ`, with the
  derivative of R10. The file states the step as `softmax (log w - η ℓ)`
  (`isMirrorDescentStep_negEntropy_iff`, with its uniqueness), the approximate steps as the points
  at relative entropy at most `ε` from it, the trajectory from the uniform point as
  `softmax (-η ∑ s < t, ℓ s)` with its uniqueness, and the invariance under adding a constant to a
  loss (`isMirrorDescentStep_negEntropy_add_const_iff`). PR #302 ports the first three claims of
  6.2 in `LMLExplore/OnlineLearning/ExponentiatedGradient.lean`, with the objective's value as one
  `IsLeast` statement (`isLeast_mul_apply_add_bregDiv_negEntropy`) and the trajectory in the
  `softmax (-(η • ∑ s < t, ℓ s))` form of `softmax_regret_le`. It drops the approximate-step lemmas,
  since `IsApproxMirrorDescentStep` is R11. It also adds `hasFDerivAt_negEntropy_pi` and
  `bregDiv_negEntropy_pi` to `LMLExplore/Analysis/Convex/NegEntropy.lean`, beside the `PiLp` forms:
  part of R10, under the local names, which PR #303 replaces by the plain ones.
- R10: LMLExplore states `hasFDerivAt_negEntropy` and `bregDiv_negEntropy` on `PiLp p`. The
  paper's statements use `negEntropy` on `α → ℝ`, with the derivative
  `∑ a, log (y a) • ContinuousLinearMap.proj a`. The refactor states both on `α → ℝ` and derives
  the `PiLp p` forms from them, since the Bregman divergence only evaluates the linear map. The
  coordinate-separable lemmas of R14 give the `α → ℝ` forms. The local file names them
  `hasFDerivAt_negEntropy_pi`, `bregDiv_negEntropy_pi` and `bregDiv_negEntropy_pi_eq` (the
  generalized relative entropy off the simplex), beside LMLExplore's `PiLp` forms; the refactor
  gives the `α → ℝ` forms the plain names. PR #303 names them `hasFDerivAt_negEntropy`,
  `bregDiv_negEntropy_of_mem_simplex` and `bregDiv_negEntropy`, renames the `PiLp p` derivative
  `hasFDerivAt_negEntropy_ofLp`, and replaces the `PiLp p` divergence on the simplex by
  `bregDiv_negEntropy_ofLp`, which equates it with the one on `α → ℝ`.
- R11: the error `ε` and the learning rate `η` are parameters of a single step, so trajectories
  with per-round errors and rates need no new definition.
- R12: the library theorem is the paper's Theorem 2 in a real normed space, with the one-step
  inequality of its proof. The headline `Schlisselberg2026Hidden.approxMirrorDescent_regret_le_of_smooth`
  stays in `SSKM2026/Theorem2.lean` as a one-line specialization. The approximate first-order
  condition is the paper's Lemma 22, with the sign of its proof corrected (erratum E15). It uses
  the descent lemma of R8.
- R13: the library theorem is the paper's Theorem 52, with its Lemma 51. The headline
  `Schlisselberg2026Hidden.approxFTRL_regret_le` stays in `SSKM2026/Theorem52.lean` as a one-line
  specialization. The item also holds the paper's Lemma 23 (`a x² - b x - c ≤ 0` implies
  `x < b / a + √(c / a)` for `a, b, c > 0`), placed beside LMLExplore's `Analysis/Real/Sqrt.lean`.
  The paper's Lemma 24 (R17) uses it too.
- R14: Definition 1 of the paper asks for the bounds on `(0, 1]`, and the Lean definition asks for
  them on `(0, 1)` (erratum E1, `notes/modelling.md`). The scalar bounds are the paper's Lemmas 21
  and 41, Lemma 41 in corrected form, with the factor `1 / (ν - 1)` (erratum E26). The strong
  convexity is for the `ℓ¹` norm on the points of the simplex with positive coordinates, with
  modulus `c₁ / 2`; the paper's proof of Theorem 6 uses modulus `1` (erratum E6). Proved so far:
  the definition, the Bregman divergence of a coordinate-separable function as a sum
  (`bregDiv_sum_apply`), Taylor's formula of order two, and all the scalar bounds (strict
  monotonicity of `r'`, Lemma 41 for `ν > 1` and `ν = 1`, the quadratic bounds on `D_r`). Still to
  do: the examples, the derivative of the coordinate-separable regularizer and its strong
  convexity.
- R15: the paper's Lemma 31 and the facts of the blueprint's `lem:polytope_facts`. Tau Ceti's
  `IsConvexPolyhedron` gives the vocabulary for the sets.
- R16–R19: the paper's own lemmas, in `SSKM2026/`, one file per result, from the blueprint
  chapters `entropy-lower` (R16), `entropy-upper` (R17), `barrier-upper` (R18) and
  `polytope-lower` (R19). R16 is the paper's Lemma 34 and its power-barrier form. R17 covers
  Lemmas 13, 21–25, 33, 39, 40 in entropy form and the balance of i.i.d. losses in the proof of
  Theorem 7. R18 covers Lemmas 10–12, 22, 26, 27, 42 and the replacement of Lemma 25 on polytopes.
  R19 covers Lemmas 43–48 and Theorem 49. R16 holds Lemma 34 for the negative entropy and for power
  barriers, and the one-dimensional bound that replaces Lemma 24 for power barriers. R17 takes the
  Bregman divergence of the negative entropy on `α → ℝ` from R10 (`bregDiv_negEntropy_pi_eq`).

## Proposed targets

### S1. Inexact mirror descent and inexact FTRL

On a set `K` of a real normed space `E`, with linear losses in the dual `E →L[ℝ] ℝ` and the
conventions of the Bandits roadmap's Layer 6:

- **Approximate steps.** A point `x ∈ K` is an `ε`-approximate step of mirror descent from `a`,
  with potential `F`, a linear map `F'` (a derivative of `F` at `a`), learning rate `η` and loss
  `y`, if `η y x + D_F(x, a) ≤ η y b + D_F(b, a) + ε` for every `b ∈ K`; the infimum need not be
  attained. Likewise an `ε`-approximate play of FTRL at round `t`, for the objective
  `η ∑_{s<t} y_s + F`. API: the `0`-approximate steps and plays are LMLExplore's
  `IsMirrorDescentStep` and `IsFTRLPlay`; monotonicity in `ε`; `ε ≥ 0`; existence for every
  `ε > 0` when the objective is bounded below on a nonempty `K` [SSKM26, Section 2, Algorithm 1].
- **The approximate first-order condition.** Let `K` be convex, let `x̂ ∈ K` be an
  `ε`-minimizer of `f` on `K`, let `f` have a derivative `f'` within `K` at `x̂`, and let
  `f y - f x̂ - f' (y - x̂) ≤ β / 2 * ‖y - x̂‖ ^ 2` on the segment `[x̂, w]`, with `β > 0`. Then
  `f' (w - x̂) ≥ -max (‖w - x̂‖ * √(2 β ε)) (2 ε)` [SSKM26, Lemma 22], corrected sign.
- **Regret of approximate mirror descent with a smooth regularizer.** For `K` convex of diameter
  at most `D`, a regularizer `1`-strongly convex on `K` with a `β`-Lipschitz derivative within
  `K` (OnlineLearning 1.3), losses of dual norm at most `1`, and errors `ε_t ≤ D² / 2`, every
  trajectory of `ε_t`-approximate steps has regret at most
  `D_F(u, x_0) / η + η n / 2 + D √(2 β) ∑_{t<n} √ε_t / η` [SSKM26, Theorem 2], with the one-step
  inequality of its proof.
- **Regret of approximate FTRL.** For `K` compact and convex, a regularizer `1`-strongly convex on
  `K` with a derivative within `K`, losses of dual norm at most `1`, an exact play at round `0` and
  `ε_t`-approximate plays at rounds `t < n`: the regret is at most
  `(F u - F x_0) / η + ∑_{t<n} (2 η + √(2 ε_t))` [SSKM26, Lemma 51, Theorem 52], with the bound
  `x < b / a + √(c / a)` for the roots of `a x² - b x - c ≤ 0` [SSKM26, Lemma 23].

Suggested home: the OnlineLearning roadmap, beside Layer 6.1, in `LMLExplore/OnlineLearning/`
and `LMLExplore/Analysis/Convex/`.

### S2. Coordinate-separable regularizers and power barriers

For a finite type `α` and `r : ℝ → ℝ`, the coordinate-separable regularizer
`R w = ∑ a, r (w a)` on `α → ℝ`:

- its derivative `∑ a, deriv r (w a) • ContinuousLinearMap.proj a` at every `w` whose coordinates
  lie in an open set on which `r` is differentiable;
- its Bregman divergence, the sum of the scalar divergences
  `D_r(y, x) = r y - r x - r' x * (y - x)` of the coordinates;
- strong convexity for the `ℓ¹` norm on the points of the simplex with positive coordinates,
  with modulus `c / 2`, when `c / x ≤ r'' x` on `(0, 1)`.

A **power barrier** with exponent `ν ≥ 1` and constants `0 < c₁`, `c₂` is a function `r` twice
differentiable on `(0, 1)` with `c₁ / x ^ ν ≤ r'' x ≤ c₂ / x ^ ν` there [SSKM26, Definition 1].
Prove that the negative entropy `x log x` (`ν = 1`, `c₁ = c₂ = 1`), the Tsallis entropies
`(x - x ^ q) / (1 - q)` for `q ∈ (0, 1)` (`ν = 2 - q`, `c₁ = c₂ = q`) and the log barrier `-log x`
(`ν = 2`, `c₁ = c₂ = 1`) are power barriers. Prove the scalar bounds [SSKM26, Lemmas 21 and 41],
Lemma 41 corrected:
- `r'` is monotone on `(0, 1)`;
- `r' y - r' x ≥ c₁ / (ν - 1) * (x ^ (1 - ν) - y ^ (1 - ν))` for `0 < x ≤ y < 1` and `ν > 1`, and
  `r' y - r' x ≥ c₁ * log (y / x)` for `ν = 1`;
- `0 ≤ D_r(y, x)`, `c₁ (y - x)² / (2 max x y) ≤ D_r(y, x)`, and `D_r(y, x) ≤ M (y - x)² / 2` when
  `r'' ≤ M` between `x` and `y`.

Suggested home: `LMLExplore/Analysis/Convex/`, for the OnlineLearning roadmap, beside Layer 6.2
and the Tsallis potentials of Bandits 7.5.

### S3. Polytopes in standard form

For a finite type `α`, a linear map `A : (α → ℝ) →ₗ[ℝ] M` and `b : M`, the polytope
`K = {w | (∀ a, 0 ≤ w a) ∧ A w = b}`:

- `K` is a convex polyhedron (Tau Ceti's `IsConvexPolyhedron`), closed, with direction `ker A`;
- for `x ∈ K` and `v ∈ ker A`, `x + v ∈ K` iff `0 ≤ x + v`, so that from a point with positive
  coordinates every direction of `ker A` can be followed for a positive time;
- the first-order condition: a convex function on `K` with a derivative within `K` at a point `x`
  of `K` with positive coordinates is minimized on `K` at `x` iff its derivative vanishes on
  `ker A` [SSKM26, Lemma 30];
- for a difference `v` of two points of the simplex, `∑ a, v a = 0`, each `|v a| ≤ ‖v‖₁ / 2`, and
  `∑ a, v a ^ 2 ≤ ‖v‖₁ ^ 2 / 2` [SSKM26, Lemma 31].

Suggested home: `LMLExplore/Analysis/Convex/`, for the OnlineLearning roadmap (mirror descent on
polytopes) and the ReinforcementLearning roadmap (occupancy polytopes).

References: [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
