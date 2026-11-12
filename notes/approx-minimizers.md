# Approximate minimizers, smooth regularizers and approximate FTRL

Decisions of the round of 2026-11-12 that proved the chapters `prereq-approx`, `smooth` and
`ftrl` (items R8, R12, R13 of `PAPER_ROADMAP.md`; Theorems 2, 3 and 52).

## Generality of the library statements

- **Lemma 22** (`LMLExplore.neg_max_le_apply_sub_of_le_add`, `ForLMLExplore/Analysis/Convex/ApproxMinimizer.lean`)
  only assumes its two inequalities on the segment `[x, w]`: `f x ≤ f z + ε` and the quadratic
  upper bound `D_f(z, x) ≤ β / 2 * ‖z - x‖ ^ 2`. It needs no convex set, no derivative (`f'` is any
  continuous linear functional) and no sign of `β`. The case `ε = 0` is handled by a limit
  `γ → 0`, so the exact first-order condition is a special case. The second claim
  (`neg_mul_sqrt_le_apply_sub_of_le_add`) takes `‖w - x‖ ≤ D` and `ε ≤ β D² / 2`.
- **Lemma 23** is stated twice in `ForLMLExplore/Analysis/Real/Sqrt.lean`: the paper's strict form
  for `a, b, c > 0`, and a non-strict form for `a > 0`, `b, c ≥ 0`. Lemma 51 needs the non-strict
  one, since `ε` may vanish. The non-strict form fails for `b < 0` (`a = c = 1`, `b = -1`).
- **The descent lemma** (`ForLMLExplore/Analysis/Convex/Smooth.lean`) is stated with a
  derivative within `K` at every point of `K` and the Lipschitz bound on `K`, and gives the
  two-sided bound `|D_f(y, x)| ≤ s / 2 * ‖y - x‖ ^ 2`. It is also stated for a function
  differentiable on an open set containing `K`, with `fderiv`: the form of OnlineLearning 1.3.
  No definition of `s`-smoothness is introduced here; the port adds the target's definition.
- **One step of approximate mirror descent** (`ForLMLExplore/OnlineLearning/ApproxMirrorDescent/Smooth.lean`):
  the base point `a` need not lie in `K`, the linear map at `a` is arbitrary and `η` has no sign.
  Two forms: with `ε ≤ β D² / 2` and no convexity (`mul_apply_sub_le_of_smooth`), and with an
  `m`-strongly convex potential and `ε ≤ m D² / 2` (`mul_apply_sub_le_of_strongConvexOn`), which
  reduces to the first since `m ≤ β` as soon as `K` has two points.
- **The regret bounds** (`approxMirrorDescent_sum_apply_sub_le`, `approxFTRL_sum_apply_sub_le`)
  have an `m`-strongly convex potential, errors `ε t` that may change with the round, and any
  losses (the bounds keep `‖y t‖`). The headline results are their case `m = 1`, `ε t = ε`,
  `‖y t‖ ≤ 1`. Their names differ from the headline names, so that the namespaces
  `LMLExplore.OnlineLearning` and `Schlisselberg2026Hidden` never make a name ambiguous.
- **Lemma 51** (`IsApproxFTRLPlay.norm_sub_le`) gives
  `‖x - w‖ ≤ 2 η ‖y t‖ / m + √(2 ε / m)` for `η ≥ 0`.

## Proof routes that differ from the paper

- Theorem 52: instead of the be-the-leader lemma on the shifted losses `R / η + ℓ_0, ℓ_1, …`,
  the proof applies LMLExplore's FTRL inequality `regret_le_ftrl` with the regularizer `R / η`, the
  exact plays of every round as leaders (the given exact play at round `0`) and the approximate
  plays as the plays whose regret is bounded. The terms left are `ℓ_t(w̃_t - w_{t+1})`, as in the
  paper.
- Theorem 2: the stability term of each round is LMLExplore's
  `apply_sub_sub_div_le_of_mul_norm_sq_le` (the paper's Lemma 27), with the strong convexity
  lower bound of the Bregman divergence; the last divergence `D_R(u, w_T)` is dropped as
  nonnegative.
