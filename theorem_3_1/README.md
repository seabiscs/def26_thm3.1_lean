# Lean formalization of Theorem 3.1

This directory contains an assumption-free Lean theorem corresponding to
Theorem 3.1 of `counter-50.pdf`.

The public theorem is:

```lean
Theorem31.theorem31
    (q : ℝ) (hq1 : 1 < q) (hq2 : q < 2) :
    Nonempty (Theorem31.Theorem31Conclusion q)
```

There is no Cauchy–Kowalevskaya hypothesis and no Section 3.3 certificate in
this theorem.  Its only hypotheses are the manuscript assumptions
`1 < q < 2`.

## Formal conclusion

`Theorem31Conclusion q` contains:

- a parameter package with exponent exactly `q`;
- a positive radius `ell` and the square `Q = (-ell, ell)^2`;
- a concrete `W^{1,∞}` representative `u` equal to
  `u(x,y) = x + y^2 * gamma(x,y)`;
- analyticity of `u` in a neighborhood of the closed square;
- identification of the recorded gradient with the actual ansatz gradient;
- `‖Du‖ ≤ 1` at every point of the closed square;
- `‖Du‖ < 1` at every off-axis point of the open square;
- `u(x,0) = x` on `[-ell,ell]`;
- the weak Euler identity for the explicit
  `W^{1,1}_0 ∩ W^{1,∞}` test class;
- pointwise off-axis identification of the integral's stress representative
  with the paper's energy-gradient stress `∂ J̃_q(Du)`;
- measurable weak-`L^{q/[2(q-1)]}` control of the stress;
- Born–Infeld maximality in the fixed Sobolev-trace Dirichlet class,
  including an explicit proof that the candidate itself belongs to that
  class; and
- the horizontal diameter as a maximally extended light ray, unique as an
  unoriented segment.

## Sobolev and trace boundary

Mathlib does not currently expose a direct standard API for the precise
bounded-domain spaces and trace operator used in the manuscript.  This
formalization therefore uses self-contained, representative-level
definitions rather than leaving a Sobolev or trace theorem as an assumption.

`W1InfinityMap ell` records:

- a Lipschitz representative on the closed square;
- an a.e. strongly measurable, essentially bounded gradient field; and
- a.e. equality of that field with the classical gradient.

`W11ZeroW1InfinityTest ell` records the standard smooth-density
presentation of `W^{1,1}_0 ∩ W^{1,∞}`: globally smooth compactly
supported approximants, `W^{1,1}` convergence of values and gradients, a.e.
gradient convergence, and a uniform gradient bound.

The fixed-trace condition for a competitor `w` is defined by the existence
of such a test-space witness representing `w - u` a.e. on the square.  Thus
the variation used in the weak Euler equation is obtained directly from the
definition; no unproved trace lemma is assumed.

The constant-zero `W1InfinityMap` and its constant-zero smooth approximating
sequence are constructed explicitly.  They prove reflexivity of the trace
relation.  Consequently every unit-gradient base map belongs to its own
Dirichlet class, and `IsBornInfeldMaximizer q u` explicitly includes
`u ∈ DirichletClass u`; maximality cannot hold merely because the admissible
class is empty.

These definitions are the formal statement's explicit function-space
boundary.  The development does not claim a separate equivalence theorem
with a Mathlib trace-space object that does not presently exist.

## Module map

- `StressTensor/` and `StressTensor.lean`: unconditional analytic
  construction of `gamma`, compact localization, gradient estimates, and
  maximal-light-ray classification (Sections 3.1–3.2).
- `MaximalityOfU.lean`: measure-theoretic weak-tail, excision, convex-energy,
  and generic maximality lemmas.
- `GammaMaximalityBridge.lean`: exact compatibility between the analytic
  construction and the variational notation.
- `BornInfeldSubgradient.lean`: convexity of `-J_q`, its concrete relative
  subgradient, and identification with the constructed energy-gradient
  stress.
- `LocalizedStressBounds.lean`: the estimates corresponding to (3.27), the
  distribution bound corresponding to (3.28), stress measurability and
  integrability, and the identity `p/2 = q/[2(q-1)]`.
- `Section33WeakEuler.lean`: excision of the light axis, rectangle integration
  by parts, vanishing interface flux, and the smooth weak Euler identity
  corresponding to (3.29)–(3.30).
- `Section33Integrability.lean`: automatic density and stress-pairing
  integrability on the finite square.
- `Theorem31Packaging.lean`: concrete function spaces, unconditional
  candidate map, explicit zero-test and self-membership witnesses, gradient
  and stress bridges, a.e. subgradient, and the maximality theorem from weak
  Euler.
- `Section33DenseEuler.lean`: dominated-convergence extension from smooth
  tests to the recorded `W^{1,1}_0 ∩ W^{1,∞}` class, corresponding to
  (3.31).
- `Theorem31.lean`: final unconditional statement and assembly.
- `Theorem31Audit.lean`: axiom audit for the public theorem.

## Build and audit

From this directory:

```sh
lake build Theorem31
lake env lean Theorem31Audit.lean
```

The full target build completes successfully in 8,788 jobs.  After the two
source linter cleanups, it completes with zero warnings.

The axiom audit prints:

```text
'Theorem31.theorem31' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

These are standard Lean/Mathlib axioms.  The source tree contains no
`sorry`, `admit`, custom `axiom`, or `sorryAx` dependency.
