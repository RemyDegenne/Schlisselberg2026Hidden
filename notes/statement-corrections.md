# Corrections of the headline statements

Errors found after phase 1 in the project's own headline statements, where the paper is right.
Each entry names the frozen statement, the problem, the evidence, when it was found, and the
user's decision (`/lml:formalize-paper decide`). The errors of the paper itself are in
`notes/paper-errata.md`.

## Theorem 6: the value of r at 1

- **Statement:** `Schlisselberg2026Hidden.approxMirrorDescent_regret_le_of_isPowerBarrier`, as
  frozen at the end of phase 1.
- **Problem:** the hypothesis `hu'` allows every comparator `u ∈ K` once `r` is right-continuous
  at `0`. The Lean definition `LMLExplore.IsPowerBarrier` asks the bounds on `(0, 1)` only
  (erratum E1), so it does not constrain `r 1`, and `r 1` enters `D_R(u, a 0)` when `u` is a
  vertex `e_i` of the simplex, which `K` may contain (for instance `K = Δ`). Lowering `r 1` makes
  `D_R(u, a 0)` as negative as one likes, and the bound false. The paper is not affected: its
  Definition 1 asks the bounds on `(0, 1]`, so its `r` is differentiable, hence continuous, at
  `1`. The phase-1 correction of E1 replaced `(0, 1]` by `(0, 1)` and restored the continuity at
  `0` only. Comparators with positive coordinates are not affected either: in dimension at least
  `2` their coordinates lie in `(0, 1)`.
- **Evidence:** `Schlisselberg2026Hidden.exists_not_regret_le_of_isPowerBarrier`
  (`SSKM2026/BarrierUpper/Theorem6Counterexample.lean`): `α = Fin 2`, `A w = w 0 + w 1`, `b = 1`
  (so `K` is the simplex), `r` the Tsallis entropy of index `1/2` changed to `-10` at `1` (a power
  barrier with `ν = 3/2`, `c₁ = c₂ = 1/2`, right-continuous at `0`, by
  `LMLExplore.IsPowerBarrier.congr`), `u = (1, 0)`, `η = 1`, `ε = 0`, `T = 0`, losses `0`, the
  constant trajectory at the uniform point. Every hypothesis holds and the regret is `0`, while the
  bound is `D_R(u, a 0) / η = -10 - 2 r (1/2) ≤ -8`.
- **What is proved:** the frozen theorem in the case `∀ i, 0 < u i`; the core form
  `Regret_T(u) ≤ (D_R(u, a 0) - D_R(u, a T)) / η + (1 + 1/c₁) η T` for every `u ∈ K`
  (`Schlisselberg2026Hidden.regret_le_sub_div_add_of_isPowerBarrier`, `η ≤ 2`, any initial point
  with positive coordinates); and the statement with the right alternative of `hu'` replaced by
  `ContinuousWithinAt r (Set.Ici 0) 0 ∧ ContinuousWithinAt r (Set.Iic 1) 1`
  (`Schlisselberg2026Hidden.approxMirrorDescent_regret_le_of_isPowerBarrier_of_continuousWithinAt`).
- **Choices:** (a) replace the right alternative of `hu'` by the two one-sided continuities above,
  which makes the headline a one-line specialization of the proved lemma (recommended; relation
  `closeMatch`, erratum E6 unchanged); (b) replace it by `ContinuousOn r (Set.Icc 0 1)`, simpler to
  read and true of the Tsallis entropies, also a one-liner from the proved lemma; (c) keep only
  comparators with positive coordinates (`narrowMatch`), which loses the vertices for the Tsallis
  entropies.
- **Found:** round of 2026-11-12 (slot 2, on top of commit a7e3b85).
- **Decision:** pending.
