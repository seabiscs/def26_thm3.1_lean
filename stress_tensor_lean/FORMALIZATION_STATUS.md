# Equation-by-equation status

“Proved” means checked by Lean with no project-defined axiom or proof
placeholder.  The final theorem is unconditional: it starts only from
`P : Params`.  The use of `Classical.choice` selects objects whose existence
has already been proved; it is not an analytic-existence assumption.

| Reference | Status | Main Lean location |
|---|---|---|
| (3.1)--(3.5) | Proved | `Ansatz` |
| (3.6) | Proved, including removable value, integral/quotient equality, the displayed truncated expansion, its `O(t^4 d^3)` remainder, and analyticity | `ScalarFactors`, `ScalarAnalyticity`, `ScalarTaylorExpansion` |
| (3.7)--(3.8) | Proved, including positivity, derivatives, and analyticity on `V_q` | `ScalarDerivatives`, `ScalarAnalyticity`, `ScalarNeighborhood` |
| (3.9)--(3.10) | Proved for the actual ansatz and stress | `Ansatz`, `ActualFieldBridge`, `LocalizationBridge` |
| (3.11)--(3.14) | Proved for the actual ansatz and original energy-gradient stress, off `y=0` | `DifferentialBridge`, `AnalyticDifferentialBridge`, `ActualFieldBridge`, `CompactLocalization` |
| (3.15)--(3.16) | Proved, including exact regrouping and axis formulas | `AuxiliaryEquation`, `AxisFormulas` |
| (3.17)--(3.18) | Proved: openness of the literal `U_q`/`V_q` neighborhoods, `U_q -> V_q`, and all component estimates | `Bounds`, `CompleteArgumentPackaging` |
| (3.19) | Proved, including base/rpow, `Ctilde`, and `Stilde` bounds | `ScalarNeighborhood` |
| (3.20) | Proved: exact derivative identity and lower bound | `ScalarDerivatives`, `ScalarNeighborhood` |
| (3.21) | Proved automatically from `InU` | `LocalizationBridge` |
| (3.22)--(3.23) | Proved: normal-form equivalence and seven-dimensional analyticity on `U_q` | `AuxiliaryEquation`, `NormalFormAnalyticity` |
| Shifted/quasilinear CK structure | Proved: exact `A*hxy+B*hyy+C` decomposition and vanishing factors | `QuasilinearNormalForm` |
| Closed first-order CK reduction | Proved: exact `(h_x,Gamma2)` system, residual equivalence, and `t=y^2` principal matrix | `FirstOrderReduction`, `CKFirstOrderVectorRHS` |
| Equation-specific formal recurrence | Proved: construction, diagonal identities, and formal uniqueness | `CKFirstOrderFormalSystem`, `CKFormalDiagonalCongruence`, `CKFormalRecurrenceDiagonalIdentity` |
| Factorial/geometric majorant | Proved unconditionally using anisotropic normalization, symmetric FMS, Nagumo composition, and transport closure | `CKBivariateRateNormalization`, `CKSymmetricBivariateFMS`, `CKFMSNagumoComposition`, `CKNagumoTransportClosure`, `CKFirstOrderCompleteConvergence` |
| Convergent analytic CK solution | Proved: power-series evaluation, termwise derivatives, PDE identity, and reconstruction | `CKFirstOrderSeriesEvaluation`, `FirstOrderReconstruction`, `CKCompleteOutcome` |
| Analytic local uniqueness | Proved by deriving the same recurrence for every analytic competitor and equality of component jets | `CKAnalyticCompetitorRecurrence`, `CKAnalyticCompetitorPDE`, `CKCompleteOutcome` |
| (3.24), Cauchy jet and local analytic outcome | Proved unconditionally | `CauchyDataBridge`, `CKCompleteOutcome` |
| Reflection/evenness | Proved unconditionally for the constructed outcome | `ReflectionBridge`, `CompleteArgument` |
| CK neighborhood `Q_0` and compact containment | Proved unconditionally: compact closure inside the analytic box and `Q_rho`, strict radius inequalities, and actual-jet membership in `U_q` | `CompactContainment` |
| Compact-square localization and (3.25) | Proved unconditionally, with off-axis divergence of the original stress | `CompactLocalization`, `FinalArgument`, `CompleteArgument` |
| Definitions (2.6)--(2.7), rigidity, and unique maximal ray | Proved unconditionally, including the cited rigidity argument | `LightRayBridge`, `FinalArgument`, `CompleteArgument` |

## End-to-end result

`CompleteArgument.exists_complete_argument` constructs positive radii and an
actual `CKOutcome`, then supplies a compact localization on which the original
stress divergence vanishes off the light axis.  It proves that the horizontal
diameter is a maximally extended light segment, that every maximally extended
light segment has that same closed segment, and that the reconstructed scalar
field is even in the transverse coordinate.

At the manuscript's original parameter boundary,
`exists_complete_argument_of_two_lt p hp` starts from the sole assumption
`2 < p`, constructs `q = p / (p - 1)` and the full `Params` package, and
returns the same complete conclusion.

## Strict scope boundary

The formalization covers the supplied Section 3.1--3.2 argument and the cited
light-ray definitions and uniqueness conclusion.  The distributional Euler
equation and proof of variational maximality from Section 3.3 were not part of
the attached subsection and are not formalized here.
