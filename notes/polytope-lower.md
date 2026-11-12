# Theorem 8: design decisions of the proof

The proof of `Schlisselberg2026Hidden.exists_approxMirrorDescent_le_integral_regret_polytope`
(chapter `polytope-lower` of the blueprint) follows `notes/constants-polytope-lower.md`, variant
8-B (Rademacher signs on the `Z`-coordinates, `ℓ(P) = μ`). Decisions taken in phase 2, 2026-11-12:

- **Index type.** The construction lives on `Fin m × Fin 5 ⊕ Fin 2` (`.inl (i, 0)` is `X i`,
  `.inl (i, k)` for `k = 1, 2, 3` is `Y k i`, `.inl (i, 4)` is `Z i`, `.inr 0` is `P`, `.inr 1` is
  `Q`), so that every sum splits block by block (`PolytopeLower.sum_coord`). `SSKM2026/Theorem8.lean`
  transports it to `Fin d` along `Fintype.equivFin`: the objective of a step, the regret, the
  divergence from the uniform point and the law of the losses are invariant.
- **The polytope by coordinates.** `PolytopeLower.polytope` is the coordinate description of the
  paper's `{w ≥ 0, A w = A u₀}`. The statement asks for a matrix: `exists_matrix_mulVec_eq_iff`
  turns the `4 m + 1` linear constraints into one. The paper's matrix and its kernel basis (Lemma
  43, erratum E29) are not formalized.
- **The trajectory in closed form.** Every play is on the curve `W(e^{η n}, q)`, so the trajectory
  is the scalar recursion `PolytopeLower.trajQ` for `q_n`. The frozen step is taken only from round
  `τ` on and only when it is `ε`-approximate; otherwise the exact step is taken. So the trajectory
  is `ε`-approximate for every loss sequence of the construction, not only on the hardness event,
  and is defined everywhere (the paper's is not defined off its event, erratum E34). On the median
  event every step after `τ` is frozen (`PolytopeLower.trajQ_le_inv`).
- **Measurability.** The level function `f(E, ·)` is continuous and strictly increasing on
  `(0, 2 / d)`, and onto `ℝ` by the intermediate value theorem; its inverse `levelInv` is
  `Function.invFunOn` and is monotone, hence measurable.
- **The expectation.** The median event `{G_n ≤ n μ}` and the vanishing of
  `E[ℓ t (Z i) · φ]` for `φ` depending on the other rounds both come from one symmetry, the sign
  flip of the `Z`-coordinates of a finite set of rounds (`PolytopeLower.measurePreserving_flipZ`).
  No independence API is needed.
- **Library-shaped leftovers.** A few small lemmas in `SSKM2026/` are not specific to the paper:
  the gap of the objective of a negative-entropy step (`PolytopeLower.objective_sub_objective`),
  the evaluation `sum_smul_proj_apply`, the transport lemmas of `Theorem8.lean` and
  `exists_matrix_mulVec_eq_iff`. They stay here: the first is the coordinate form of R10, which
  another round owns, and the others are a few lines each.
