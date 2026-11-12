# Blueprint outline

The contract between the blueprint chapters and the Lean files of the formalization of [SSKM26]
(arXiv:2511.22283v2, `source/arXiv-2511.22283v2/`). It fixes the labels, the Lean names, the
modelling (`notes/modelling.md`) and the proof routes. The detailed, constant-by-constant proof
routes of the four hardest areas are in `notes/constants-*.md`; the blueprint chapters follow
them.

## Headline results (decided with the user, 2026-11-12)

| Paper | Blueprint label | Lean name (namespace `Schlisselberg2026Hidden`) | File |
| --- | --- | --- | --- |
| Theorem 2 | `thm:ub_smooth` | `approxMirrorDescent_regret_le_of_smooth` | `SSKM2026/Theorem2.lean` |
| Theorem 3 | `thm:lb_smooth` | `exists_approxMirrorDescent_le_regret_euclidean` | `SSKM2026/Theorem3.lean` |
| Theorem 4 | `thm:lb_barrier_adversarial` | `exists_approxMirrorDescent_le_regret_negEntropy` | `SSKM2026/Theorem4.lean` |
| Theorem 5 | `thm:up_barrier_adversarial` | `approxMirrorDescent_regret_le_negEntropy` | `SSKM2026/Theorem5.lean` |
| Theorem 6 | `thm:ub_nonentropy` | `approxMirrorDescent_regret_le_of_isPowerBarrier` | `SSKM2026/Theorem6.lean` |
| Theorem 7 | `thm:ub_barrier_stochastic` | `approxMirrorDescent_regret_le_negEntropy_iid` | `SSKM2026/Theorem7.lean` |
| Theorem 8 | `thm:lb_nonsimplex` | `exists_approxMirrorDescent_le_integral_regret_polytope` | `SSKM2026/Theorem8.lean` |
| Lemma 14 | `lem:balance_lower_bound` | `exists_approxMirrorDescent_le_regret_of_balanced` | `SSKM2026/Lemma14.lean` |
| Lemma 15 | `lem:balance_upper_bound` | `approxMirrorDescent_regret_le_negEntropy_of_balanced` | `SSKM2026/Lemma15.lean` |
| Theorem 35 | `thm:dimension_lower_bound` | `exists_approxMirrorDescent_le_regret_of_isPowerBarrier` | `SSKM2026/Theorem35.lean` |
| Theorem 36 | `thm:three_phase_lower_bound` | `exists_approxMirrorDescent_le_regret_negEntropy_threePhase` | `SSKM2026/Theorem36.lean` |
| Theorem 52 | `thm:approx_ftrl` | `approxFTRL_regret_le` | `SSKM2026/Theorem52.lean` |

Every other numbered result of the paper is a blueprint item (lemma) of the proof that uses it,
not a comparator target.

## What exists

Searched in LMLExplore 469c4c5 (and through it LML, Tau Ceti, Mathlib), up to renaming and
generalization:

- **Bregman divergence**: LML `bregDiv f x y J = f x - f y - J (x - y)`, with
  `bregDiv_three_point` (the paper's Lemma 26), `bregDiv_add_swap`.
- **Mirror descent**: LMLExplore `IsMirrorDescentStep K F η y a F' x` (exact steps),
  `IsMirrorDescentStep.mul_apply_sub_le` (the one-step inequality), `exists_isMirrorDescentStep`,
  `mirrorDescent_regret_le_bregDiv_div`, `mirrorDescent_regret_le_of_strongConvexOn`.
- **FTRL**: LMLExplore `IsFTRLPlay`, `exists_ftrl`, `sum_le_of_isMinOn_sum` (be-the-leader, the
  paper's Lemma 50), `bregDiv_le_sub_of_isMinOn` (first-order condition at a minimizer).
- **Strong convexity**: Mathlib `StrongConvexOn`; LMLExplore
  `StrongConvexOn.mul_norm_sub_sq_le_bregDiv`, `apply_sub_sub_div_le_of_mul_norm_sq_le` (the
  paper's Lemma 27).
- **Regret**: LMLExplore `regret ℓ x u n = ∑ t < n, (ℓ t (x t) - ℓ t u)`.
- **Simplex and negative entropy**: LMLExplore `simplex α`, `uniform_mem_simplex`,
  `negEntropy` (unnormalized), `hasFDerivAt_negEntropy`, `bregDiv_negEntropy` (relative
  entropy), `strongConvexOn_negEntropy` (ℓ¹, `PiLp 1`), `softmax` (multiplicative weights:
  the exact step of mirror descent with the negative entropy on the simplex),
  `isFTRLPlay_negEntropy_iff`, the Gibbs variational principle
  `isGreatest_sum_sub_mul_sub_sum_mul_log_div_div`.
- **Taylor for Bregman divergences**: LMLExplore `Convex.exists_mem_segment_bregDiv_eq`.
- **Concentration**: Mathlib sub-Gaussian MGFs and Hoeffding
  (`ProbabilityTheory.measure_sum_ge_le_of_iIndepFun`, `HasSubgaussianMGF`), Gaussian laws
  (`gaussianReal`, `gaussianReal_map_add`, sums of independent Gaussians).

Missing, and library-shaped (`ForLMLExplore/`):
- approximate mirror descent steps and approximate FTRL plays (stated, with their basic API);
- the approximate first-order condition of an ε-minimizer under a quadratic upper bound (the
  paper's Lemma 22) and the quadratic upper bound of a function with Lipschitz derivative;
- power barriers (the paper's Definition 1), with the examples, and the coordinate-separable
  regularizer: gradient, Bregman divergence as a sum, strong convexity on the simplex for ℓ¹;
- standard-form polytopes `{w ≥ 0, A w = b}`: first-order conditions at interior minimizers (the
  paper's Lemma 30), the existence and positivity of the minimizer of a barrier objective.

## Chapters

Part I, following the paper (the balance lemmas of Section 5.1 and the step-size lemmas of
Appendix A are proved, in corrected form, inside the chapters that use them):
1. `setting` — Section 2: approximate steps and trajectories (`def:approx_step`), power barriers
   (`def:power_barrier`), positivity of the iterates.
2. `smooth` — Section 3, Appendix B: `lem:smooth_one_step`, Theorem 2, Lemma 27
   (`lem:omd_helper`), Theorem 3.
3. `entropy-lower` — Section 5.3, Appendix D: Lemma 34 (`lem:entropy_stuck`,
   `lem:barrier_stuck`), Lemma 14, Theorems 4, 35, 36. Detailed route:
   `notes/constants-lower-bounds.md`.
4. `entropy-upper` — Appendix E: Lemmas 21–25, 13, 33, 39, 40 (entropy forms), Lemma 15,
   Theorems 5, 7. Detailed route: `notes/constants-entropy-upper.md`.
5. `barrier-upper` — Sections 5.1, 5.2, Appendix F: Lemmas 10–12, 21, 22, 41, 42, the
   replacement of Lemma 25 on polytopes (`lem:bar_pull_to_start`), Theorem 6. Detailed route:
   `notes/constants-barrier-polytope.md`.
6. `polytope-lower` — Appendix G: Lemmas 43–48, Theorem 49, Theorem 8 (Rademacher losses).
   Detailed route: `notes/constants-polytope-lower.md`, variant 8-B.
7. `ftrl` — Appendix H: Lemma 51, Theorem 52 (Lemma 50 is LMLExplore's be-the-leader).

Part II, library-shaped:
- `prereq-approx` — approximate steps, Lemmas 22, 23, the quadratic upper bound of a function
  with Lipschitz derivative.

## Modelling decisions taken after the constants review

- Barrier results (Theorems 6, 35) take their steps on the points with positive coordinates of
  the polytope or simplex: `r 0` is a junk value in Lean, and comparing with boundary points would
  make positive steps impossible for the log barrier (E1).
- Theorem 4 is stated for every `η > 0` (regret `T/10`); Lemma 14 and Theorem 36 need `η ≤ 1`.
- Theorem 7 uses the threshold `δ/(6d³T⁴)` (variant (7c), `δ/(1000d²T⁴)` under `T ≥ d`, not
  taken).
- Theorem 8 uses the Rademacher law (variant 8-B, user decision), with the polytope existential
  and its dimension bounded by `100 log(1/ε)`, and the i.i.d. sequence as `Measure.infinitePi`.
