# Errata of "The Hidden Cost of Approximation in Online Mirror Descent"

Errors found in O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The Hidden Cost of
Approximation in Online Mirror Descent*, arXiv:2511.22283v2 (18 June 2026), while formalizing it
in Lean. Each entry gives where the error is (the result of v2, its label in the TeX source), the
error, the correction, the Lean declaration that states the corrected form, the kind of error and
when it was found. Entries are numbered `E1`, `E2`, … and never renumbered. Numbers of results
are those of v2 (definitions, theorems and lemmas share one counter).

The details of the corrected proofs, with every constant derived, and the scripts of the numerical
checks quoted below are in the repository's `notes/constants-*.md`. Rounds are numbered from 1 here,
as in the paper.

Kinds: typo, wrong constant, missing hypothesis, gap in the proof, false statement.

## E1. Definition 1: the log barrier is not a real-valued function on [0, 1]

- **Where:** Definition 1 (`def:nu_barrier`), Section 2, and the list of examples after it.
- **Error:** the definition asks for a real-valued, twice-differentiable `r : [0,1] → ℝ` with
  `c₁/x^ν ≤ r''(x) ≤ c₂/x^ν` on `(0, 1]`. No such `r` is differentiable at `0` (`r' → -∞`), and the
  log barrier `-log x`, listed as an example, is not real-valued at `0`. For a comparator `w` on the
  boundary of `K`, `D_R(w, w₁)` is then `+∞` for the log barrier.
- **Correction:** ask the bounds on `(0, 1)` (all iterates and segments between them have
  coordinates in `(0, 1)` when `d ≥ 2`), take the OMD subproblems over the points of `K` with
  positive coordinates (the domain of the barrier), and state the regret bounds for comparators
  with positive coordinates, or for all comparators when `r` is right-continuous at `0` and
  left-continuous at `1`. The bounds on `(0, 1)` say nothing about `r(1)`, which enters `D_R(w, w₁)`
  at a vertex `w` of the simplex; the paper's bounds on `(0, 1]` make `r` continuous at `1`.
- **Lean:** `LMLExplore.IsPowerBarrier`; `Schlisselberg2026Hidden.approxMirrorDescent_regret_le_of_isPowerBarrier`
  and `Schlisselberg2026Hidden.exists_approxMirrorDescent_le_regret_of_isPowerBarrier` take their
  steps on the points with positive coordinates.
- **Kind:** missing hypothesis.
- **Found:** phase-1 statement check, 2026-11-12.

## E2. Theorem 4: the proof applies a two-arm lemma to d arms, and needs η ≤ 1

- **Where:** Theorem 4 (`thm:lb_barrier_adversarial`), Section 4.1; its proof in Section 5.3.
- **Error:** the proof is "Lemma 14 with `α = T/3`", but Lemma 14 is for `d = 2` while Theorem 4
  is for `d ≥ 2`; padding the extra coordinates with loss `1` loses the compensation that the
  regret count needs (E10). Lemma 14 itself needs `η ≤ 1` (E10), while Theorem 4 has no condition
  on `η`. The initial point is not stated (the proof uses the uniform one; a lower bound with a
  free start is trivial).
- **Correction:** for `η ≤ 1`, Lemma 14 in the corrected form of E10 (any `d ≥ 2`, first-phase
  loss on the future best arm only) gives regret at least `T/6` for every `T`, with the uniform
  start. For `η > 1`, exact OMD on the alternating losses `1 - e_{i₂}`, `1 - e_{i₁}`, … already has
  regret at least `⌈T/2⌉/2 - ⌊T/2⌋/(1 + e^η) ≥ T/10`. So the theorem holds for every `η > 0`
  with regret at least `T/10`.
- **Lean:** `Schlisselberg2026Hidden.exists_approxMirrorDescent_le_regret_negEntropy`.
- **Kind:** gap in the proof.
- **Found:** phase-1 statement check, 2026-11-12.

## E3. Theorem 5 is false for losses in [-1, 1]^d

- **Where:** Theorem 5 (`thm:up_barrier_adversarial`), Section 4.1; its proof in Section 5.3 ("Any
  adversarial sequence over the simplex is `T/2`-balanced").
- **Error:** for losses in `[-1, 1]^d` the balance of a loss sequence can be `T`, not `T/2` (a
  coordinate can lead by `T` on the first half and trail on the second). The theorem is false:
  with `d = 2`, `η = T^{-1/2}`, `ε` at the theorem's threshold, losses `(1, -1)` for about `T/4`
  rounds (exact steps) and then `(-1, 1)` (staying put is `ε`-approximate), the regret is about
  `T` (`3.8·10⁵` at `T = 4·10⁵`), while `log 2/η + C η T = O(√T)` for every constant `C`. The
  hidden `\opt{…}` version of the proof in the source has the correct "`T`-balanced, `α = T`".
- **Correction:** for losses in `[0, 1]^d`, any sequence is `T/2`-balanced
  (`L^{i*}_{[s,t)} - L^i_{[s,t)} ≤ min(t - s, T - (t - s))`) and the theorem holds with its
  `e^{-ηT/2}` (with the constants of E4). For losses in `[-1, 1]^d` the threshold must be
  `e^{-ηT}`.
- **Lean:** `Schlisselberg2026Hidden.approxMirrorDescent_regret_le_negEntropy`, for losses in
  `[0, 1]^d`.
- **Kind:** false statement.
- **Found:** phase-1 statement check, 2026-11-12.

## E4. Theorem 5 and Lemma 15: threshold, comparator term and initialization

- **Where:** Theorem 5, Lemma 15 (`lem:balance upper bound`), Section 5.3, and their proofs in
  Section 5.3 and Appendix E.
- **Error:**
  - The threshold of Theorem 5, `(1/(6d)) e^{-ηT/2} min{η⁴, T^{-2}}`, drops the `1/η` branch of
    Lemma 15's `1/(d max{6e^{ηα}, 1/η})`, so it does not imply Lemma 15's threshold with
    `α = T/2` (e.g. `η = 1/16`, `T = 3`).
  - With the corrected Lemmas 24, 25, 33 and 40 (E16, E17, E19, E25) the factor `6` is not enough:
    `32e ≈ 87` is needed. In the proof of Lemma 15, "`ε ≤ 1/(16de^{αη+1}T²) =
    1/(r''(1/16de^{αη+1})T²)`" has `16` for `2`.
  - Both results claim `D_R(w, w₁)/η` for every `w ∈ K`, but the proofs (Lemma 39) bound only the
    regret against the best vertex `w*`, which gives `D_R(w*, w₁)/η = log d/η`.
  - Neither states the initial point; Lemmas 39 and 40 use the uniform one. It cannot be dropped:
    with losses `(0, 1)`, `η = T^{-1/2}` and `w₁ = (e^{-0.6√T}, ·)`, staying put is
    `ε`-approximate at the corrected threshold for `T ≥ 10⁵` and has regret `≈ T`, against
    `D_R(e₁, w₁)/η + ηT ≈ 0.6 T`.
- **Correction:** with the uniform start, `0 < η ≤ 1/16`, and
  `ε ≤ e^{-ηα} min{η⁴, T^{-2}}/(100d)` (Lemma 15; `α = T/2` for Theorem 5), the regret against
  every point of the simplex is at most `log d/η + ηT`. `T ≥ 3` is not needed. The proof is a new
  proof of Lemma 39 (E24).
- **Lean:** `Schlisselberg2026Hidden.approxMirrorDescent_regret_le_negEntropy_of_balanced`,
  `Schlisselberg2026Hidden.approxMirrorDescent_regret_le_negEntropy`.
- **Kind:** wrong constant; missing hypothesis.
- **Found:** phase-1 statement check, 2026-11-12.

## E5. Theorem 6: a simplex lemma is used on polytopes

- **Where:** Theorem 6 (`thm:ub_nonentropy`), Section 4.1; the sketch in Section 5.2 and Lemma 42
  (`lem:nonentropy_iterate_lb`), Appendix F ("from Lemma 25, we know for start that
  `w_t^i ≥ ψ/2`").
- **Error:** Lemma 25 (`lem:not_too_far`) is stated and proved on the simplex only: its proof (via
  Lemma 24) compares `w_{t+1}` with a point that moves mass between arbitrary coordinates, which in
  general leaves a polytope `K`. The induction of Lemma 42 applies it on `K`.
- **Correction:** compare `x = w_{t+1}` with `z = (1 - λ)x + λw₁ ∈ K` for `λ = ψ/2`. The
  approximate optimality of `x` and the convexity of the objective give
  `⟨∇φ_t(z), w₁ - x⟩ ≥ -ε/λ`; with the balance accumulated so far this bounds
  `⟨∇R(w₁) - ∇R(z), w₁ - z⟩ ≤ 4ηT`, hence `z ≥ ψ` coordinatewise (Lemma 12) and `x ≥ ψ/2`. This
  needs no exact minimizer and no condition on `η`. (Whether Lemma 25's conclusion fails on
  polytopes is not settled; a random search found no counterexample.)
- **Lean:** `Schlisselberg2026Hidden.approxMirrorDescent_regret_le_of_isPowerBarrier`; the
  replacement of Lemma 25 is `Schlisselberg2026Hidden.half_le_of_forall_isApproxMirrorDescentStep`.
- **Kind:** gap in the proof.
- **Found:** phase-1 statement check, 2026-11-12.

## E6. Theorem 6: threshold, constant and the final computation

- **Where:** Theorem 6 and its proof in Appendix F.
- **Error:**
  - Lemma 42 says the theorem's assumption is `ε ≤ η⁴ min{c₂, 1/c₂}(ψ/2)^ν`; the theorem's
    threshold equals this times `2^{ν - ν/(ν-1)}`, which exceeds `1` for `ν > 2` (`2.83` at
    `ν = 3`). With the corrected Lemma 41 (E26) the lower bound `ψ` changes as well (E27).
  - The proof applies Lemma 27, which assumes `R` 1-strongly convex, but a `ν`-barrier is only
    `c₁/2`-strongly convex for `‖·‖₁` on the positive part of the simplex. The constant in
    `O(ηT)` must depend on `c₁`: with `T = 1`, `ε = 0`, `K = Δ₂`, `r = -c log x`, `η = √c`,
    `ℓ₁ = (1, -1)`, `w = (0.01, 0.99)` and `c = 10⁻⁸`, the regret is `0.98` while
    `D_R(w, w₁)/η = 3.2·10⁻⁴`, which forces the constant above `9796`.
  - The final computation applies Lemma 22 with `w = w*` and `β = c₂/ψ^ν` on the whole segment
    `[w_{t+1}, w*]`, but `w*` has zero coordinates, where `r''` is unbounded.
  - Several steps of Lemma 42 (`ε ≤ ηψ^ν`, `ε ≤ c₂ψ/4`, `T√(c₂ε(2/ψ)^ν) ≤ ηT`) need `η ≤ 1`, which
    `η ≤ 1/(16c₁)` does not give when `c₁ < 1/16`.
- **Correction:** with `Ψ = (2d)^{ν-1} + 8(ν-1)ηTd/c₁`, `ψ = Ψ^{-1/(ν-1)}`, any `η > 0`, and
  `ε ≤ η⁴ψ^ν/(4^{ν+2} max{1, c₂})`, the iterates stay above `ψ` and the regret is at most
  `D_R(u, w₁)/η + (1 + 1/c₁)ηT`, using the first-order condition only on the half of the segment
  towards `u` near `w_{t+1}`. Neither threshold implies the other.
- **Lean:** `Schlisselberg2026Hidden.approxMirrorDescent_regret_le_of_isPowerBarrier`.
- **Kind:** wrong constant; gap in the proof.
- **Found:** phase-1 statement check, 2026-11-12.

## E7. Theorem 7: the range of T, the random best arm and the threshold

- **Where:** Theorem 7 (`thm:ub_barrier_stochastic`), Section 4.2; its proof in Section 5.3.
- **Error:**
  - `T ≥ 256` does not give `η = √(log d/T) ≤ 1/16`, which Lemma 15 needs, once `d ≥ 3`
    (`d = 3`, `T = 256`: `η = 0.0655`).
  - The balance is taken with respect to the empirical best arm `i*`, which is random: Hoeffding's
    inequality for a fixed pair of arms does not apply, and `L^{i*}_{[s,t)} - L^i_{[s,t)}` has a
    drift `(t - s)(μ^{i*} - μ^i)`.
  - "`ηα ≤ log(dT²/δ)`" fails when `log d` is large compared with `log(T²/δ)` (e.g. `log d = 20`,
    `T = 256 log d`, `δ = 1/2`: even the sharp `√(2 log d log(N/δ))`, with `N` the number of
    events of the union bound, is `48.1 > 37.8`).
  - For `d = 2`, `min{η⁴, T^{-2}} = (log 2)²/T²`, so the threshold `δ/(6d²T⁴)` overstates what
    Lemma 15 gives by `2.08` even granting the previous step.
- **Correction:** Hoeffding's inequality for the bridges
  `(L^i - L^j)_{[s,t)} - ((t - s)/T)(L^i - L^j)_{[0,T)}` (mean `0`, sub-Gaussian parameter at most
  `T`) and a union bound give, with probability `1 - δ`, balance at most
  `A = √(2T log(d²(T+1)²/δ))` with respect to every best arm, and `e^{ηA} ≤ d²(T+1)/√δ`. With
  `T ≥ 256 log d` and `ε ≤ δ/(6d³T⁴)`, the regret is at most `2√(T log d)`. (Under `T ≥ d`,
  `ε ≤ δ/(1000d²T⁴)` suffices.)
- **Lean:** `Schlisselberg2026Hidden.approxMirrorDescent_regret_le_negEntropy_iid`.
- **Kind:** missing hypothesis; gap in the proof; wrong constant.
- **Found:** phase-1 statement check, 2026-11-12.

## E8. Theorem 8: the order of the quantifiers, the range of ε and the D_R term

- **Where:** Theorem 8 (`thm:lb_nonsimplex`), Section 4.2; its proof in Appendix G.
- **Error:**
  - "There exists a polytope `K ⊆ Δ_d` and a distribution of losses such that for any `ε > 0`
    …": the construction's `K` depends on `ε` (`m = 16 log(1/ε)`, `d = 5m + 2`) and the law on `ε`
    and `η` (the mean `√(ηd)`). The dimension must be part of the claim: in dimension
    `d ≥ η²e^η/ε`, staying at the uniform point is `ε`-approximate for constant losses (Theorem
    35), which gives linear regret on the simplex itself.
  - "For any `ε > 0`" cannot hold: as `ε → 1` the bound `T√(η/log(1/ε))` exceeds `2T`, the largest
    regret for bounded losses; the proof also assumes `ε < 4η`, `m ≥ 128 log(2T)` and `d ≤ 1/η`
    ("there's a known lower bound for `Tη`", neither proved nor cited).
  - The term `D_R(w, w₁)/η` is not proved anywhere (Theorem 49 only gives `T√(η/log(1/ε))`). It
    holds for the comparator of the construction when `ηT ≥ 1`, and fails when `ηT < 0.26`.
  - The losses are Gaussian, hence unbounded, outside the standing assumption `‖ℓ_t‖_* ≤ 1` and
    the class `[-1, 1]^d` of Theorem 7, which Theorem 8 contrasts with. The noise is not needed.
- **Correction:** for every `η > 0` and `0 < ε ≤ 1/3` with `100η log(1/ε) ≤ 1`, there are a
  polytope `K ⊆ Δ_d` of the paper's form with `d ≤ 100 log(1/ε)` containing the uniform point, a
  law of losses in `[-1, 1]^d` (the paper's, with Rademacher signs for its centred Gaussians and its
  coordinate of mean `√(ηd)` made constant), an `ε`-approximate trajectory depending measurably on
  the past losses and a comparator `w*` with `E[Regret_T(w*)] ≥ T√(η/log(1/ε))/20`, and
  `≥ D_R(w*, w₁)/(6η) + T√(η/log(1/ε))/20` when `ηT ≥ 1`. The proof is repaired as in E28–E34.
- **Lean:** `Schlisselberg2026Hidden.exists_approxMirrorDescent_le_integral_regret_polytope`.
- **Kind:** false statement (as written); missing hypothesis; gap in the proof.
- **Found:** phase-1 statement check, 2026-11-12.

## E9. Lemma 10: the losses are shifted by one round

- **Where:** Lemma 10 (`lem:polytope balance`), Section 5.1, and its proof in Appendix C.
- **Error:** `B^v(t₁, t₂) = η⟨ℓ_{t₁:t₂}, v⟩` should be `η⟨ℓ_{t₁:t₂-1}, v⟩`: the optimality condition
  of round `t'` links `w_{t'-1}` and `w_{t'}` through `ℓ_{t'-1}`, and the proof sums over
  `t' ∈ [t₁, t₂]` instead of `[t₁ + 1, t₂]`. The displayed optimality condition lacks the factor
  `η`.
- **Correction:** `B^v(t₁, t₂) = η⟨ℓ_{t₁:t₂-1}, v⟩` for exact trajectories with positive iterates.
- **Lean:** not stated separately; the corrected proofs use one-step inequalities (blueprint
  `lem:bar_balance`, `lem:entropy_balance`). On polytopes:
  `Schlisselberg2026Hidden.sum_deriv_sub_mul_le_of_forall_isApproxMirrorDescentStep`.
- **Kind:** typo.
- **Found:** phase-1 statement check, 2026-11-12.

## E10. Lemma 14: order of choices, regret count, range of η

- **Where:** Lemma 14 (`lem:balance lower bound`), Section 5.3, and its restatement and proof in
  Appendix D.
- **Error:**
  - The statement fixes the losses before `ε`, but the proof's phase length
    `τ = (1/η)log(4η/ε)` depends on `ε`, and is not an integer.
  - The regret count ("`Ω(T - τ)` … adding the first `τ` steps we get `Ω(T - 2τ)`") gives
    `(T - τ)/2 - τ = (T - 3τ)/2`, negative for `τ > T/3`: the stuck weight `w^1_τ ≤ ε/(4η)` is
    only at most `1/2` when `ε` is not much smaller than `η`.
  - The proof relies on Lemma 34, false for large `η` (E20); with this construction the error of
    staying put exceeds `4ηe^{-ηα}` from `η ≈ 1.3`.
  - The initial point is not stated, `α ≥ 0` is implicit, the appendix restatement has
    "`α ≥ T/2`" for `α ≤ T/2`, and the lemma is for `d = 2` while Theorem 4 needs `d ≥ 2`.
- **Correction:** for `d ≥ 2`, `0 < η ≤ 1`, `0 ≤ α ≤ T/2` and `τ = ⌊α⌋`: the losses `e_{i₁}` for
  `τ` rounds and then `1 - e_{i₁}` are `α`-balanced with best arm `i₁`; exact steps for `τ` rounds
  and then staying put form, from the uniform point, an `ε`-approximate trajectory for every
  `ε ≥ 4ηe^{-ηα}` (the error of staying is at most `η² e^{-ητ}`); and the regret is at least
  `(1 - 1/d)(T - 2α) ≥ (T - 2α)/2`, the learner paying at least the stuck weight in the first
  phase.
- **Lean:** `Schlisselberg2026Hidden.exists_approxMirrorDescent_le_regret_of_balanced`.
- **Kind:** gap in the proof; missing hypothesis.
- **Found:** phase-1 statement check, 2026-11-12.

## E11. Lemma 11: the effective smoothness and a factor √2

- **Where:** Lemma 11 (`lem:trajectory diff`), Section 5.1, and its restatement and proof in
  Appendix C; Lemma 21 and Definition 20 as used there.
- **Error:**
  - On the segment `[ŵ_t, ŵ_t + ψv]` with `‖v‖₁ = 1` and `∑ v = 0`, the coordinates go down to
    `ψ/2` (`|v^i| ≤ 1/2`), so the effective smoothness is `c₂(2/ψ)^ν`, not `c₂/ψ^ν`.
  - The induction step adds `√(2c₂ε/ψ^ν)` per round but the statement claims `√(c₂ε/ψ^ν)`.
  - The main text puts the lower bound `ψ` on the exact trajectory, the appendix on the approximate
    one, which is what the proof uses; the exact trajectory plays no role.
- **Correction:** for `‖v‖₁ = 1`,
  `B̂^v(t₁, t₂) ≤ η⟨ℓ_{t₁:t₂-1}, v⟩ + (t₂ - t₁)(√(2^ν c₂ε/ψ^ν) + 2ε/ψ)` when the approximate iterates
  stay above `ψ` on the support of `v`.
- **Lean:** blueprint `lem:bar_one_step_balance`, `lem:entropy_balance`; for the negative
  entropy, `Schlisselberg2026Hidden.log_sub_log_add_le_of_isApproxMirrorDescentStep_negEntropy` compares
  directly with `η (ℓ j - ℓ i)`; on polytopes
  `Schlisselberg2026Hidden.sum_deriv_sub_mul_le_of_isApproxMirrorDescentStep`.
- **Kind:** wrong constant.
- **Found:** phase-1 statement check, 2026-11-12.

## E12. Lemma 13: typos in the proof

- **Where:** Lemma 13 (`lem:simplex_coordinate_bounds`), proof in Appendix C.
- **Error:** "Since `w_{t₂}^i ≥ w_{t₂}^i`" should be `w_{t₂}^i ≥ w_{t₁}^i`; the contradiction
  hypothesis `e^k w_{t₂}^{i*} < w_{t₁}^{i*}` should have `e^{k/c₁}`.
- **Correction:** as indicated; the statement is correct.
- **Lean:** `Schlisselberg2026Hidden.le_exp_mul_of_log_sub_log_add_le` and
  `Schlisselberg2026Hidden.le_exp_mul_of_log_sub_log_add_le'` (blueprint
  `lem:entropy_coordinate_bounds`).
- **Kind:** typo.
- **Found:** phase-1 statement check, 2026-11-12.

## E13. Section 5.3: the sign of the balance on the simplex

- **Where:** Section 5.3, paragraph before "Implications for the main theorems".
- **Error:** "if for every `i ∈ [d]` we have `ℓ^i_{t₁:t₂} - ℓ^{i*}_{t₁:t₂} ≤ α`, it follows that the
  loss sequence is `α`-balanced": the proofs (Lemmas 13, 40, Definition 32) use the other sign,
  `ℓ^{i*} - ℓ^i ≤ α`, and a one-sided bound does not give the two-sided notion of Section 5.1.
  The two notions also differ by a factor `2` (`‖e_{i*} - e_i‖₁ = 2`).
- **Correction:** state Lemmas 14, 15 with the one-sided notion `L^{i*}_{[s,t)} - L^i_{[s,t)} ≤ α`.
- **Lean:** the balance hypotheses of
  `Schlisselberg2026Hidden.approxMirrorDescent_regret_le_negEntropy_of_balanced` and the balance
  conclusion of `Schlisselberg2026Hidden.exists_approxMirrorDescent_le_regret_of_balanced`.
- **Kind:** typo.
- **Found:** phase-1 statement check, 2026-11-12.

## E14. Definitions 16 and 17: the objective of a step

- **Where:** Definitions 16, 17, Appendix A.
- **Error:** the objective is written `η⟨ℓ_t, w⟩ + D_R(w_{t-1}, w)`, over `Δ_d`; Section 2 has
  `η⟨ℓ_t, w⟩ + D_R(w ‖ w_t)` over `K`.
- **Correction:** `φ_t(w) = η⟨ℓ_t, w⟩ + D_R(w, w_t)` over `K`.
- **Lean:** `LMLExplore.OnlineLearning.IsApproxMirrorDescentStep`.
- **Kind:** typo.
- **Found:** phase-1 statement check, 2026-11-12.

## E15. Lemma 22: a sign

- **Where:** Lemma 22 (`lem:epsilon optimality conditions`), proof, Appendix A.
- **Error:** the second case concludes `∇f(ŵ)(w - ŵ) ≥ ‖w - ŵ‖√(2βε)`.
- **Correction:** `≥ -‖w - ŵ‖√(2βε)`.
- **Lean:** `LMLExplore.neg_max_le_apply_sub_of_le_add` (in `ForLMLExplore/`) proves the corrected
  bound, blueprint `lem:approx_first_order`.
- **Kind:** typo.
- **Found:** phase-1 statement check, 2026-11-12.

## E16. Lemma 24: a factor √2, and the curvature on the segment

- **Where:** Lemma 24 (`lem:max step`), Appendix A.
- **Error:**
  - From `ε ≥ (h/2)x² - 2ηx`, Lemma 23 with `a = h/2`, `b = 2η`, `c = ε` gives
    `x < 4η/h + √(2ε/h)`, not `√(ε/h)`. The statement is false: negative entropy, `d = 1000`,
    `w = u₀`, zero loss, `η = 10⁻⁸`, `ε = 10⁻⁶`: an `ε`-step moves a coordinate by
    `4.503·10⁻⁵ > 3.233·10⁻⁵`.
  - `h = min{r''(w_t^i), r''(w_{t+1}^i)}` bounds `r''` on the segment only if `r''` is monotone
    (Definition 18, not Definition 1); for a `ν`-barrier take `h = c₁/max{w_t^i, w_{t+1}^i}^ν`.
- **Correction:** `|w_t^i - w_{t+1}^i| ≤ 4η/h + √(2ε/h)` with `h` a lower bound of `r''` on the
  segment.
- **Lean:** `Schlisselberg2026Hidden.sub_le_of_isApproxMirrorDescentStep_negEntropy` (blueprint
  `lem:entropy_step_size`) states the corrected form, for the negative entropy.
- **Kind:** wrong constant (false statement); gap in the proof.
- **Found:** phase-1 statement check, 2026-11-12.

## E17. Lemma 25: the constant c₁ is on the wrong side

- **Where:** Lemma 25 (`lem:not_too_far`), Appendix A, equations (6)–(8).
- **Error:** from Lemma 24 with `h ≥ c₁/w_t^i`, the proof writes
  `w_{t-1}^i ≥ w_t^i - 4c₁ηw_t^i - √(c₁εw_t^i)`, where `4ηw_t^i/c₁` and (with E16)
  `√(2εw_t^i/c₁)` are meant. So the conclusion `w_{t±1}^i ≥ w_t^i/2` needs `η ≤ c₁/16` and
  `ε ≤ c₁w_t^i/32`, not `η ≤ 1/(16c₁)` and `ε ≤ (w_t^i)^ν/(16c₁)`; with the stated hypotheses and
  `ν = c₁ = 1` the argument gives only `w_{t±1}^i ≥ 0.40 w_t^i`. "`r''(w_t^i) ≥ w_t^i`" should be
  `≥ c₁/w_t^i`.
- **Correction:** `η ≤ c₁/16`, `ε ≤ c₁w_t^i/32` (for the negative entropy the stated conclusion
  holds numerically, with exact thresholds `0.098 w_t^i` and `0.135 w_t^i`).
- **Lean:** `Schlisselberg2026Hidden.div_two_le_of_isApproxMirrorDescentStep_negEntropy` (blueprint
  `lem:entropy_step_size`) states the corrected form, for the negative entropy.
- **Kind:** wrong constant.
- **Found:** phase-1 statement check, 2026-11-12.

## E18. Lemma 30: typos

- **Where:** Lemma 30 (`lem:polytope optimality`), proof, Appendix C.
- **Error:** "`w - αv ∈ Δ_d`" should be "`w* - αv ∈ K`", and `∇f(ŵ)` should be `∇f(w*)`.
- **Correction:** as indicated.
- **Lean:** not used.
- **Kind:** typo.
- **Found:** phase-1 statement check, 2026-11-12.

## E19. Lemma 33 is false

- **Where:** Lemma 33 (`lem:simplex_trajectory_diff`), Appendix C.
- **Error:** it is called a direct consequence of Lemma 11 for `v = e_{i*} - e_i`, but
  `‖e_{i*} - e_i‖₁ = 2`, so even granting Lemma 11 the error is `2(t₂ - t₁)√(ε/ψ)`. One-step
  counterexample with `d = 3`, zero loss, `T = 1`: the error is `1.9995 √(ε/ψ)` under all the
  hypotheses.
- **Correction:** `B̂^i(t₁, t₂) ≤ B^i(t₁, t₂) + (t₂ - t₁)√(8ε/ψ)` for `ε ≤ 2ψ`, with the lower
  bound `ψ` needed only for `t₁ < t ≤ t₂`.
- **Lean:** `Schlisselberg2026Hidden.log_sub_log_add_le_sum_add_one` (blueprint `lem:entropy_balance`)
  states the corrected form, for the negative entropy.
- **Kind:** false statement.
- **Found:** phase-1 statement check, 2026-11-12.

## E20. Lemma 34 is false

- **Where:** Lemma 34 (`lem:stuck`), Appendix D.
- **Error:**
  - The proof applies Lemma 24 with `h = r''(w_t^i)` at the current point; the exact step moves
    the stuck coordinate up, where `r''` is smaller, so the bound goes the wrong way.
  - From `|w_t^i - w̃^i| ≤ ε` it concludes `φ(w_t) ≤ φ(w̃) + ε`; the argument gives `ηε`.
  - Counterexamples: negative entropy, `d = 2`, `η = 10`, `ε = 0.1`, `w = (ε/(4η), ·)`, loss
    `(0, 1)`: the error of staying is `4.0015 > ε`; `r = 0.01 x log x`, `η = 1`, `ε = 0.04`:
    `0.908 > ε`; log barrier, `η = 100`: the error is `178ε`.
- **Correction:** for losses constant off coordinate `i`, `η ≤ c₁(w^i)^{1-ν}/(3ν)` and
  `ε ≥ 2η²(w^i)^ν/c₁`, staying put is `ε`-approximate (comparing with points with positive
  coordinates). For the negative entropy and the loss `1 - e_{i₀}`, staying is `ε`-approximate as
  soon as `ε ≥ η²min(m, 1 - m)` (`η ≤ 1`, `m = w^{i₀}`), by the closed form
  `log(1 + m(e^η - 1)) - ηm` of the error.
- **Lean:** `Schlisselberg2026Hidden.isApproxMirrorDescentStep_negEntropy_self` (negative
  entropy) and `Schlisselberg2026Hidden.isApproxMirrorDescentStep_self_of_isPowerBarrier` (power
  barriers, from the one-dimensional bound
  `Schlisselberg2026Hidden.mul_abs_sub_sub_le_of_isPowerBarrier`, which compares with the curvature
  along the whole step), both in `SSKM2026/Lemma34.lean`.
- **Kind:** false statement.
- **Found:** phase-1 statement check, 2026-11-12.

## E21. Theorem 35 is false for large η

- **Where:** Theorem 35 (`thm:dimension lower bound`), Appendix D.
- **Error:** the proof has the error of E20 (curvature at the wrong end of the step), and the
  theorem has no condition on `η`. It fails: negative entropy, `d = 1000`, `η = 7`,
  `ε = 4η²/d = 0.196`: the uniform point is not an `ε`-minimizer (error `0.733`). For the proof's
  loss the best `ε`-approximate trajectory has per-round regret `0.033`. The initial point, the
  loss range and the regret constant are not stated.
- **Correction:** for `0 < η ≤ c₁d^{ν-1}/(3ν)` and `ε ≥ 4η²/(c₁d^ν)` (the paper's threshold; the
  proof gives `(e/2)η²/(c₁d^ν)`), staying at the uniform point is `ε`-approximate for the constant
  losses `1 - e_{i₀}`, with regret `T(1 - 1/d) ≥ T/2`. Only the lower bound `c₁` is used.
- **Lean:** `Schlisselberg2026Hidden.exists_approxMirrorDescent_le_regret_of_isPowerBarrier`.
- **Kind:** false statement.
- **Found:** phase-1 statement check, 2026-11-12.

## E22. Theorem 36: integrality, range of η and regret count

- **Where:** Theorem 36 (unlabelled, after Theorem 35), Appendix D.
- **Error:** the phase lengths `k/(2η)`, `3k/(2η)`, `k/η` need not be integers; the proof uses
  Lemma 34 (E20), and with this trajectory the error of staying exceeds `4ηe^{-ητ}` from
  `η ≈ 2.7`; the last regret step ("this are `3T/4` steps") ignores the comparator's loss `2τ`;
  the statement omits what the theorem is about (the exact trajectory keeps weight at least
  `1/2` on the optimal arm) and the start `(1/2, 1/2)`.
- **Correction:** with `τ ∈ ℕ` (`k = 2ητ`), `0 < η ≤ 1` and `T ≥ 40τ`: one trajectory is
  `ε`-approximate for every `ε ≥ 4ηe^{-ητ}`, the losses are `2τ`-balanced, every exact trajectory
  keeps weight at least `1/2` on the optimal arm, and the regret is at least
  `(T - 9τ)/2 ≥ T/3`. The identity `w_{4τ} = (1/2, 1/2)` is correct.
- **Lean:** `Schlisselberg2026Hidden.exists_approxMirrorDescent_le_regret_negEntropy_threePhase`.
- **Kind:** missing hypothesis; gap in the proof.
- **Found:** phase-1 statement check, 2026-11-12.

## E23. Lemma 38: hypotheses and direction

- **Where:** Lemma 38 (`lem:not_too_far_phi`), Appendix E.
- **Error:** it assumes `η ≤ 1/4` but applies Lemma 25, which needs `η ≤ 1/16`; it uses the
  constant of Lemma 24 (E16); `r''(ŵ_t^{i*})` should be `r''(ŵ_t^i)`; and it bounds the `i`-th
  component of `∇φ_t(ŵ_t)` from above, while Lemma 39 needs a lower bound.
- **Correction:** not needed by the corrected proof of Lemma 39 (E24).
- **Lean:** not used.
- **Kind:** gap in the proof.
- **Found:** phase-1 statement check, 2026-11-12.

## E24. Lemma 39: gaps in the proof

- **Where:** Lemma 39 (`lem:LB best UB regret`), Appendix E, equations (9)–(11).
- **Error:**
  - `w̃_t` sets the coordinates of `S_t` to `0`, so the segment `[ŵ_t, w̃_t]` reaches `0` and its
    effective smoothness is infinite, not `r''(ξ')`.
  - The bound on `(ηℓ^{i*} + ∇R(ŵ_t)^{i*} - ∇R(ŵ_{t-1})^{i*})(w̃^{i*} - 1)` needs a lower bound on
    the `i*` component of `∇φ_t`, which Lemma 38 does not give.
  - In (10) the three-point terms `-D_r(ŵ_t^i, ŵ_{t-1}^i)`, present only for the rounds with
    `i ∈ S_t`, are replaced by the sum over all rounds, which decreases the right-hand side.
  - The telescoping pairs `(s_j - 1, t_j)` where `(s_{j+1} - 1, t_j)` is meant; the round `T` is
    missing from `∑_{t=2}^T`; and the conclusion holds only for `w*` (E4).
- **Correction:** a new proof: the approximate first-order condition in the direction of the
  vertex, `h = e_{i*} - ŵ_t`, costs `ε/u + u(1 - ŵ_t^{i*})/ŵ_t^{i*}`, which is at most `η²/2` for
  `u = η²ξ/4` when `ŵ_t^{i*} ≥ ξ` and `ε ≤ η⁴ξ/16`; with the three-point identity and Pinsker's
  inequality, the regret against `e_{i*}` is at most `log d/η + ηT`. The sets `S_t` and Lemmas 37,
  38 are not needed.
- **Lean:** `Schlisselberg2026Hidden.sum_sum_mul_sub_le_of_le_apply` and
  `Schlisselberg2026Hidden.regret_le_of_le_apply` (blueprint `lem:entropy_regret_best_arm`), with the
  new proof.
- **Kind:** gap in the proof.
- **Found:** phase-1 statement check, 2026-11-12.

## E25. Lemma 40: constants

- **Where:** Lemma 40 (`lem:balance to bounded optimal arm`), Appendix E.
- **Error:** the statement has `T ≥ 4`, the proof "since `T ≥ 3`"; with the corrected Lemmas 25
  and 33, `ε ≤ 1/(r''(ξ/2)T²) = ξ/(2T²)` is not enough: the proof needs `ε ≤ ξ/32` (Lemma 25) and
  `ε ≤ ξ/(16T²)` (balance at most `k + 1`); "`1/(16 r''(ŵ_{t-1}^i))`" should have `ŵ_{t-1}^{i*}`;
  "some `i ∈ [d]`" should be `i ≠ i*`.
- **Correction:** `ε ≤ ξ/(32T²)`, any `T ≥ 1`.
- **Lean:** `Schlisselberg2026Hidden.exp_neg_div_card_le_apply_of_balanced` (blueprint
  `lem:entropy_best_arm_lower`) states the corrected form.
- **Kind:** wrong constant.
- **Found:** phase-1 statement check, 2026-11-12.

## E26. Lemma 41 is false for ν > 2

- **Where:** Lemma 41 (`lem:gradient_diff`), Appendix F.
- **Error:** it is stated as an equality, `r'(w₂) - r'(w₁) = c₁/w₁^{ν-1} - c₁/w₂^{ν-1}`, while the
  proof gives an inequality, and the integral drops a factor:
  `∫_{w₁}^{w₂} c₁w^{-ν} dw = (c₁/(ν - 1))(w₁^{1-ν} - w₂^{1-ν})`. Without the factor the inequality
  fails for `ν > 2` (for `r'' = x^{-3}`: `4998 < 9996`).
- **Correction:** `r'(w₂) - r'(w₁) ≥ (c₁/(ν - 1))(w₁^{1-ν} - w₂^{1-ν})` for `0 < w₁ ≤ w₂ < 1`.
- **Lean:** blueprint `lem:barrier_scalar`.
- **Kind:** false statement.
- **Found:** phase-1 statement check, 2026-11-12.

## E27. Lemma 42 is false for ν > 9

- **Where:** Lemma 42 (`lem:nonentropy_iterate_lb`), Appendix F, and the `ψ` of Section 5.2.
- **Error:** the lower bound `w_t^i ≥ ψ = (c₁/(8ηTd + c₁(2d)^{ν-1}))^{1/(ν-1)}` fails already for
  exact OMD on `Δ₂`: `ν = 11`, `c₁ = c₂ = 1`, `η = 1/16`, losses `(1, -1)`, `T = 5·10⁶`:
  `w_T^1 = 0.209128 < ψ = 0.209814`. It is a consequence of E26.
- **Correction:** `ψ = ((2d)^{ν-1} + 8(ν - 1)ηTd/c₁)^{-1/(ν-1)}`, under the threshold of E6.
- **Lean:** blueprint `lem:bar_iterates_lower`,
  `Schlisselberg2026Hidden.le_of_forall_isApproxMirrorDescentStep`.
- **Kind:** false statement.
- **Found:** phase-1 statement check, 2026-11-12.

## E28. Appendix G: integrality and unneeded assumptions

- **Where:** Appendix G, "Polytope definition" and "General settings and hardness event".
- **Error:** `m = 16 log(1/ε)` and `τ = 3/η` are not integers; the assumption `ε < 4η` only
  serves the flawed step of E33.
- **Correction:** `m = ⌈16 log(1/ε)⌉`, `τ = ⌈3/η⌉` (then `e^{-m/16} ≤ ε`, `3 ≤ ητ < 3 + η`); drop
  `ε < 4η`.
- **Lean:** `Schlisselberg2026Hidden.exists_approxMirrorDescent_le_integral_regret_polytope`.
- **Kind:** typo.
- **Found:** phase-1 statement check, 2026-11-12.

## E29. Lemma 43: the matrix is not in echelon form

- **Where:** Lemma 43 (`lem:A ker`), Appendix G.
- **Error:** "A is already in echelon form": rows `A_i` and `A_{m+i}` have the same leading column.
  `A` has full rank `4m + 1` nevertheless.
- **Correction:** each group of rows has a private coordinate once `A_{m+i}` is eliminated.
- **Lean:** not used (the corrected proof describes `K` by coordinates).
- **Kind:** typo.
- **Found:** phase-1 statement check, 2026-11-12.

## E30. Lemma 45: the hardness event

- **Where:** Lemma 45, Appendix G.
- **Error:** with `τ = 3/η` the mean and variance of `G` are `3√(d/η)` and `3(m+1)/η`, not
  `2√(d/η)` and `2(m+1)/η`; `P(G ≤ 0) = Φ(-√(3d/(m+1)))` is between `5·10⁻⁵` and `9.2·10⁻⁵`;
  Hoeffding's inequality is applied to Gaussians, without centring, with a threshold too small by a
  factor `2` and "w.p. `1/(2T)`" for "except with probability `1/(2T)`" (numerically the failure
  probability is `0.064` against the claimed `0.0078`); and the union bound controls the second
  part of `E` only up to probability `1/2 > P(G ≤ 0)`, so `P(E) = Ω(1)` does not follow.
- **Correction:** the median event `{G_τ ≤ E G_τ}` (probability at least `1/2` by symmetry), with
  the sharpened Lemma 47 (E32), which tolerates `ηG_τ ≤ 3.02`.
- **Lean:** `Schlisselberg2026Hidden.PolytopeLower.half_le_measureReal_sum_le_zero` (the median
  event), used by `Schlisselberg2026Hidden.exists_approxMirrorDescent_le_integral_regret_polytope`.
- **Kind:** gap in the proof; wrong constant.
- **Found:** phase-1 statement check, 2026-11-12.

## E31. Lemma 46: typos in the proof

- **Where:** Lemma 46 (`lem:first cors high`), Appendix G.
- **Error:** "Assume by contradiction that `w_τ^i ≥ 3/d`" should be "suppose `w_τ^i < 3/d`";
  "`w_t^{m+i} = w_t^{2m+i} = w_t^{m+i}`" should end with `w_t^{3m+i}`; Lemma 10 is applied with
  `τ` losses to `w_τ` (E9).
- **Correction:** the statement is true; in fact `w_τ^i = e^{η(τ-1)}w_τ^{m+i}`.
- **Lean:** `Schlisselberg2026Hidden.PolytopeLower.curveY_ge`, in the proof of Theorem 8.
- **Kind:** typo.
- **Found:** phase-1 statement check, 2026-11-12.

## E32. Lemma 47: signs

- **Where:** Lemma 47 (`lem:polytope stuck base`), Appendix G.
- **Error:** the statement has `e^{m/8}` for `e^{-m/8}`; in the proof "`w_τ^i ≤ 1/(2d)`" is false
  (`d w_τ^i ∈ [1.89, 2]`), and the ratio bounds `≥ 2`, `≤ 2.5` should be `≥ 1/2`, `≤ 1/2.5`; as
  written the derivation yields the useless `w_τ^{5m+2} ≤ e^{m/8}`.
- **Correction:** with the signs fixed it gives `e^{-m/8}/d`; a sharpened form,
  `w_τ^{5m+2} ≤ (2/d)(2/ρ_τ)^m e^{ηG_τ}`, needs only `ηG_τ ≤ 3.02` instead of `G_τ ≤ 0`.
- **Lean:** `Schlisselberg2026Hidden.PolytopeLower.levelInv_le` (the sharpened form), in the proof
  of Theorem 8.
- **Kind:** typo.
- **Found:** phase-1 statement check, 2026-11-12.

## E33. Lemma 48: the approximate step

- **Where:** Lemma 48 (`lem:polytope stuck step`), Appendix G.
- **Error:** `⟨ℓ_t, v_i⟩` is `-3`, not `-1`; the argument that the exact step increases the first
  coordinates writes `3 log((w_t^i - ε)/w_t^i)` and concludes `-η ≥ log(1 - ε/4) ≥ -ε/4`, where
  `1 - ε/4` has no source and `log(1 - x) ≥ -x` is false; it uses the event `E` of E30; membership
  of the modified point in `K` is not checked.
- **Correction:** an explicit "frozen" step that keeps the last coordinate, whose suboptimality is
  at most `q h(r)` in closed form (`h(r) = e^{-r} - 1 + r`); no comparison with the exact step.
- **Lean:** `Schlisselberg2026Hidden.PolytopeLower.isApproxMirrorDescentStep_curve` (the exact and
  frozen steps), in the proof of Theorem 8.
- **Kind:** gap in the proof.
- **Found:** phase-1 statement check, 2026-11-12.

## E34. Theorem 49: the expectation

- **Where:** Theorem 49, Appendix G.
- **Error:** the expected loss is computed on `E`, but `E` depends on the losses of the same
  rounds, and `E^c` is ignored (the trajectory is not defined there); only the rounds `t ≥ τ` are
  counted, which needs `T ≥ 2τ`; the comparator remark forgets the coordinates `[4m + 1, 5m]`,
  which also have nonzero loss (they are zeroed too).
- **Correction:** each play depends on the past losses only, so it is independent of the loss of
  its round and `E⟨ℓ_t, w_t⟩ = ⟨E ℓ_t, E w_t⟩`: the expected regret is computed exactly, and the
  median event bounds it below at every round.
- **Lean:** `Schlisselberg2026Hidden.PolytopeLower.integral_regret_eq` (the exact expectation), used
  by `Schlisselberg2026Hidden.exists_approxMirrorDescent_le_integral_regret_polytope`.
- **Kind:** gap in the proof.
- **Found:** phase-1 statement check, 2026-11-12.

## E35. Algorithm 1: the FTRL objective

- **Where:** Algorithm 1, Appendix H.
- **Error:** `φ_t(w) = η∑_{s=1}^t ⟨w_t, ℓ_t⟩ + R(w)` has `w_t, ℓ_t` for `w, ℓ_s`.
- **Correction:** `φ_t(w) = η∑_{s=1}^t ⟨w, ℓ_s⟩ + R(w)`.
- **Lean:** `LMLExplore.OnlineLearning.IsApproxFTRLPlay`.
- **Kind:** typo.
- **Found:** phase-1 statement check, 2026-11-12.
