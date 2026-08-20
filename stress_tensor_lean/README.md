# Stress-tensor formalization

This private Lean 4 project gives a self-contained formalization of the
manuscript-specific argument in Sections 3.1--3.2 of the supplied reference
(PDF pages 5--8, equations (3.1)--(3.25)), together with the light-ray
definitions and uniqueness conclusion cited from Section 2.3.

The analytic Cauchy--Kowalevskaya step is proved inside the project.  The
construction starts from the exact first-order reduction, builds its formal
coefficient recurrence, proves an anisotropic Nagumo/FMS majorant, evaluates
the resulting convergent power series, verifies the PDE, and proves local
uniqueness against analytic competitors.  Thus `CKOutcome` is still useful as
a modular interface, but `CKCompleteOutcome.positiveCKOutcomeData` now
constructs an inhabitant unconditionally for every `Params` value.

The main final entry points are:

```lean
StressTensor.CompleteArgument.exists_complete_argument (P : Params)
StressTensor.exists_complete_argument_of_two_lt (p : ℝ) (hp : 2 < p)
```

The second theorem constructs the manuscript's conjugate exponent
`q = p / (p - 1)` automatically.  These results supply positive local radii,
the analytic solution, compact localization, off-axis vanishing of the
original energy-gradient stress divergence, the unique maximally extended
horizontal light segment, and transverse evenness.

The project contains no `sorry`, `admit`, custom axiom, or `unsafe`
declaration.  A kernel axiom audit of the final theorem reports only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound` principles.

## Build

The project is pinned to Lean 4.33.0 and Mathlib 4.33.0.  With `elan`
installed, run:

```sh
lake build
```

`lake-manifest.json` records the exact dependency revisions used by the
successful local build.

## What Lean proves

- The ansatz derivatives, squared-gradient identity, deficit factorization,
  and stress factorization in (3.1)--(3.10).
- Equality of the integral and removable-quotient definitions of `Ctilde`,
  the displayed two-term Taylor expansion with its literal
  `O(t^4 d^3)` remainder, and analyticity of `Ctilde` and `Stilde`
  throughout `V_q`.
- Every estimate in (3.17)--(3.21), including `1/4 < Ctilde < 4`,
  `Stilde >= 1/8`, `Gamma1 >= 1/2`, and `c0 >= (q-1)/1024`.
- The actual chain- and product-rule expansions (3.13)--(3.14), their
  regrouping into (3.15)--(3.16), the axis extension, and the off-axis
  divergence identity for the original energy-gradient stress.
- Analyticity and exact quasilinear structure of the seven-dimensional normal
  form, followed by the closed first-order system for
  `(v,r)=(h_x,Gamma2)` and the even coordinate `t=y^2`.
- The equation-specific formal recurrence, its unconditional
  factorial/geometric convergence estimate via normalized symmetric
  formal-multilinear-series and Nagumo bounds, and termwise analytic series
  realization.
- Verification that the evaluated series solves the reduced PDE,
  reconstruction of `h`, the original Cauchy data, and analytic uniqueness by
  equality of all first-order component jets.
- Reflection invariance and evenness, compact-square localization, uniform
  spacelike-gradient estimates, light-segment rigidity, maximality of the
  horizontal diameter, and uniqueness of that maximally extended light ray.
- Openness of the literal seven-dimensional `U_q` and two-dimensional `V_q`
  neighborhoods, and compact containment of the final closed square in both
  the analytic reconstruction box and `Q_rho`, with its actual jet in `U_q`.

## Module map

| Modules | Contents |
|---|---|
| `Definitions`, `Ansatz` | Parameters, jets, ansatz, gradient/deficit/stress identities |
| `ScalarFactors`, `ScalarDerivatives`, `ScalarAnalyticity`, `ScalarTaylorExpansion`, `ScalarNeighborhood` | Integral representation, exact Taylor tail and big-O remainder, derivatives, analyticity, positivity, and scalar bounds on `V_q` |
| `AuxiliaryEquation`, `AxisFormulas`, `Bounds`, `LocalizationBridge` | Polynomial PDE, axis formulas, numerical estimates, and automatic `c0` positivity |
| `DifferentialBridge`, `AnalyticDifferentialBridge`, `ActualFieldBridge` | Actual calculus, the original/factored stress identity, and divergence |
| `NormalFormAnalyticity`, `QuasilinearNormalForm`, `FirstOrderReduction`, `FirstOrderFieldBridge`, `FirstOrderReconstruction` | Exact analytic normal form, first-order reduction, PDE bridge, and reconstruction |
| `CKFormalRecursion` through `CKFirstOrderFormalSystem` | Formal recurrence, Taylor normalization, differentiated bivariate series, and equation-specific coefficient system |
| `CKNagumoMajorant`, `CKFMSNagumoComposition`, `CKSymmetricBivariateFMS`, `CKBivariateRateNormalization`, `CKPolarScaling`, `CKSmallParameter`, `CKNagumoTransportClosure` | Normalized analytic composition and transport majorants |
| `CKNormalizedPhase`, `CKNormalizedResidualMajorant`, `CKNormalizedResidualScaling`, `CKFormalDiagonalCongruence`, `CKFormalRecurrenceDiagonalIdentity` | Exact residual estimates and the bridge back to the original recurrence |
| `CKFirstOrderVectorRHS`, `CKFirstOrderCompleteConvergence`, `CKFirstOrderSeriesEvaluation` | Unconditional convergence and analytic evaluation of the formal solution |
| `CKAnalyticCompetitorRecurrence`, `CKAnalyticCompetitorPDE`, `CKLocalBox`, `CKCompleteOutcome` | Analytic-competitor uniqueness, local box selection, and unconditional construction of `CKOutcome` |
| `ReflectionBridge`, `CompactLocalization`, `LightRayBridge`, `FinalArgument`, `CompleteArgument` | Symmetry, localization, unique maximal light ray, and the unconditional end-to-end theorem |
| `CompactContainment`, `CompleteArgumentPackaging` | Literal compact containment, openness of `U_q`/`V_q`, the canonical parameter package for every `p > 2`, and the public exponent-level theorem |

Import `StressTensor` to use the complete development.

## Scope and confidentiality

The supplied subsection invokes, but does not contain, the distributional
Euler equation and the variational maximality proof from Section 3.3.  Those
later results are outside this project's stated scope and are not claimed
here.

The supplied PDF and pasted source text are not part of this project or its
archive.  No attachment, source excerpt, or project file has been committed,
pushed, published, or uploaded to a public service.
