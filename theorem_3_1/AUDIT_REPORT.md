# Audit report: Theorem 3.1

## Result

The principal declaration

```lean
Theorem31.theorem31
    (q : ℝ) (hq1 : 1 < q) (hq2 : q < 2) :
    Nonempty (Theorem31.Theorem31Conclusion q)
```

is unconditional beyond the stated range of `q`.  In particular, it has no
input for `gamma`, no Cauchy–Kowalevskaya outcome, no localization input, no
stress estimate, no Euler identity, and no variational certificate.

## Checks performed

### Construction and geometry

- `CompleteArgument.exists_complete_argument` constructs the analytic
  solution and compact localization without an external CK assumption.
- The final candidate is definitionally the constructed ansatz.
- Its recorded gradient is proved equal to the actual coordinate gradient
  on the closed square.
- The closed-square unit bound, strict off-axis bound, axis value, maximal
  horizontal ray, and uniqueness of the maximal ray are transported from the
  authoritative localization and light-ray modules.

### Stress

- `LocalizedStressBounds.lean` proves the singular power bound, local strong
  measurability, Bochner integrability, and the distribution-function weak
  tail.
- The exponent is rewritten exactly as `q / (2 * (q - 1))`.
- `Theorem31Conclusion.stress_eq_energy_gradient_off_axis` explicitly
  identifies the zero-on-axis stress representative, away from the axis,
  with the energy-gradient stress computed from the actual ansatz gradient.
- The omitted axis has two-dimensional Lebesgue measure zero; this is proved
  before the a.e. subgradient conclusion is formed.

### Weak Euler identity

- The smooth identity is obtained by exact rectangle integration by parts on
  the two excised components.
- The normal flux tends to zero with exponent `1 - 2/p > 0`.
- The central-strip term tends to zero using stress integrability and
  absolute continuity of the integral.
- The dense extension is a dominated-convergence proof using the a.e.
  gradient convergence and uniform gradient bound stored in the test class.

### Maximality

- `BornInfeldSubgradient.lean` proves the relative supporting-hyperplane
  inequality for the convex density `-J_q` inside the closed unit ball.
- This subgradient is identified pointwise off the axis with the constructed
  stress and hence holds a.e. on the square.
- Candidate density integrability, competitor density integrability, and
  integrability of the stress paired with the gradient difference are proved
  from finite measure, measurability, unit-gradient bounds, and stress
  integrability.
- The fixed-trace definition supplies the `W^{1,1}_0 ∩ W^{1,∞}`
  variation directly.  Weak Euler cancels the linear term, giving
  minimization of `-J_q` and therefore maximization of `J_q`.
- A constant-zero `W1InfinityMap` and constant-zero smooth approximation
  witness are constructed explicitly.  They prove trace reflexivity and
  `u ∈ DirichletClass u` for every unit-gradient base map.  The definition
  of `IsBornInfeldMaximizer` includes this membership as its first conjunct,
  ruling out vacuous maximality through an empty competitor class.

## Function-space interpretation

The theorem is stated using explicit local definitions because Mathlib has no
direct bounded-domain Sobolev trace-space API matching the manuscript.

- `W1InfinityMap` is a Lipschitz representative with a measurable,
  essentially bounded a.e. classical gradient.
- `W11ZeroW1InfinityTest` is the smooth-density presentation used in the
  manuscript's weak-* extension.
- Equal trace means that `w-u` has a witness in this zero-trace density class.
- The zero witness proves that this relation is reflexive and that the
  candidate's Dirichlet class is nonempty.

This is a definition of the formal theorem's function spaces, not a residual
hypothesis.  No claim is made that an equivalence with a separate Mathlib
Sobolev/trace object has been formalized.

## Mechanical verification

Commands:

```sh
lake build Theorem31
lake env lean Theorem31Audit.lean
rg -n --glob '*.lean' --glob '!.lake/**' \
  '^\s*(sorry|admit|axiom)\b|:=\s*(by\s+)?(sorry|admit)\b' .
```

Observed results:

- full build: success, 8,788 jobs, zero warnings after linter cleanup;
- axiom audit: `[propext, Classical.choice, Quot.sound]` only;
- placeholder/custom-axiom scan: no matches.

## Scope

The audit establishes that the Lean declaration is complete for the explicit
representative and density definitions above and that every analytic,
measure-theoretic, variational, and geometric field in
`Theorem31Conclusion` is constructed.  It intentionally does not claim a
separate library-level identification with a nonexistent standard Mathlib
trace-space type.
