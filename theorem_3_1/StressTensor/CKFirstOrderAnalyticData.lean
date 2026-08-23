import StressTensor.CKAnalyticMajorant
import StressTensor.FirstOrderReduction
import Mathlib.Tactic.FinCases

/-!
# Analytic coefficient germs for the reduced first-order CK system

The closed reduction has state `U=(v,r)` and principal matrix
`firstOrderPrincipalCore`.  This file bundles its matrix and source as
finite-dimensional analytic maps and extracts the quantitative local formal
multilinear-series data used by a nonlinear majorant construction.
-/

namespace StressTensor

noncomputable section

/-- The two-component state `(v,r)` of the reduced system. -/
abbrev FirstOrderState := Fin 2 → ℝ

/-- A normed function-space presentation of a two-by-two operator.  Mathlib's
`Matrix` type intentionally carries no canonical normed-space instance, so
the analytic/majorant layer uses this definitionally identical array type. -/
abbrev FirstOrderOperator := Fin 2 → Fin 2 → ℝ

/-- The principal matrix viewed in its normed array model. -/
def firstOrderPrincipalArray (P : Params) (w : FirstOrderPhase) :
    FirstOrderOperator :=
  fun i j => firstOrderPrincipalCore P w i j

/-- The even-coordinate principal matrix in the normed array model. -/
def evenFirstOrderPrincipalArray (P : Params) (w : FirstOrderPhase) :
    FirstOrderOperator :=
  fun i j => evenFirstOrderPrincipalCore P w i j

/-- The derivative-free source vector in the reduced system. -/
def firstOrderSourceVector (P : Params) (w : FirstOrderPhase) : FirstOrderState :=
  ![firstOrderSourceRate P w, w 1 - 1]

/-- The reduced two-by-two principal matrix is analytic at every point of
the manuscript's coefficient neighborhood. -/
theorem analyticAt_firstOrderPrincipalArray
    {P : Params} {w : FirstOrderPhase} (hU : FirstOrderPhaseInU P w) :
    AnalyticAt ℝ (firstOrderPrincipalArray P) w := by
  have hA := analyticAt_firstOrderCoeffA hU
  have hB := analyticAt_firstOrderCoeffB hU
  have hr : AnalyticAt ℝ (fun u : FirstOrderPhase => u 2) w :=
    (ContinuousLinearMap.proj (R := ℝ) (2 : Fin 3)).analyticAt w
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  fin_cases i <;> fin_cases j
  · have h := hr.mul hA
    apply h.congr
    exact Filter.Eventually.of_forall fun u => by
      simp [firstOrderPrincipalArray, firstOrderPrincipalCore, Pi.mul_apply]
  · have h := (analyticAt_const :
        AnalyticAt ℝ (fun _ : FirstOrderPhase => (2 : ℝ)) w).mul hB
    apply h.congr
    exact Filter.Eventually.of_forall fun u => by
      simp [firstOrderPrincipalArray, firstOrderPrincipalCore, Pi.mul_apply]
  · simpa [firstOrderPrincipalArray, firstOrderPrincipalCore] using
      (analyticAt_const :
        AnalyticAt ℝ (fun _ : FirstOrderPhase => (1 : ℝ) / 2) w)
  · simpa [firstOrderPrincipalArray, firstOrderPrincipalCore] using
      (analyticAt_const :
        AnalyticAt ℝ (fun _ : FirstOrderPhase => (0 : ℝ)) w)

/-- The derivative-free source vector is analytic on the same neighborhood. -/
theorem analyticAt_firstOrderSourceVector
    {P : Params} {w : FirstOrderPhase} (hU : FirstOrderPhaseInU P w) :
    AnalyticAt ℝ (firstOrderSourceVector P) w := by
  have hc := analyticAt_firstOrderSourceRate hU
  have hv : AnalyticAt ℝ (fun u : FirstOrderPhase => u 1) w :=
    (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 3)).analyticAt w
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · simpa [firstOrderSourceVector] using hc
  · have h := hv.sub
      (analyticAt_const :
        AnalyticAt ℝ (fun _ : FirstOrderPhase => (1 : ℝ)) w)
    apply h.congr
    exact Filter.Eventually.of_forall fun u => by
      simp [firstOrderSourceVector, Pi.sub_apply]

/-- The even-coordinate principal matrix is analytic as well. -/
theorem analyticAt_evenFirstOrderPrincipalArray
    {P : Params} {w : FirstOrderPhase} (hU : FirstOrderPhaseInU P w) :
    AnalyticAt ℝ (evenFirstOrderPrincipalArray P) w := by
  have hA := analyticAt_firstOrderCoeffA hU
  have hB := analyticAt_firstOrderCoeffB hU
  have hr : AnalyticAt ℝ (fun u : FirstOrderPhase => u 2) w :=
    (ContinuousLinearMap.proj (R := ℝ) (2 : Fin 3)).analyticAt w
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  fin_cases i <;> fin_cases j
  · have htwo : AnalyticAt ℝ
        (fun _ : FirstOrderPhase => (2 : ℝ)) w := analyticAt_const
    have h := htwo.mul (hr.mul hA)
    apply h.congr
    exact Filter.Eventually.of_forall fun u => by
      change 2 * (u 2 * firstOrderCoeffA P u) =
        2 * u 2 * firstOrderCoeffA P u
      ring
  · have hfour : AnalyticAt ℝ
        (fun _ : FirstOrderPhase => (4 : ℝ)) w := analyticAt_const
    have h := hfour.mul hB
    apply h.congr
    exact Filter.Eventually.of_forall fun u => by
      simp [evenFirstOrderPrincipalArray, evenFirstOrderPrincipalCore,
        Pi.mul_apply]
  · simpa [evenFirstOrderPrincipalArray, evenFirstOrderPrincipalCore] using
      (analyticAt_const :
        AnalyticAt ℝ (fun _ : FirstOrderPhase => (1 : ℝ)) w)
  · simpa [evenFirstOrderPrincipalArray, evenFirstOrderPrincipalCore] using
      (analyticAt_const :
        AnalyticAt ℝ (fun _ : FirstOrderPhase => (0 : ℝ)) w)

/-- Quantitative formal-series data for the reduced principal matrix at the
distinguished Cauchy point. -/
theorem exists_firstOrderPrincipalArray_origin_localAnalyticMajorant
    (P : Params) :
    Nonempty (LocalAnalyticMajorant
      (firstOrderPrincipalArray P) firstOrderOrigin) :=
  exists_localAnalyticMajorant_of_analyticAt
    (analyticAt_firstOrderPrincipalArray (firstOrderOrigin_inU P))

/-- Quantitative formal-series data for the reduced source vector. -/
theorem exists_firstOrderSourceVector_origin_localAnalyticMajorant
    (P : Params) :
    Nonempty (LocalAnalyticMajorant
      (firstOrderSourceVector P) firstOrderOrigin) :=
  exists_localAnalyticMajorant_of_analyticAt
    (analyticAt_firstOrderSourceVector (firstOrderOrigin_inU P))

/-- Quantitative formal-series data for the even-coordinate principal
matrix. -/
theorem exists_evenFirstOrderPrincipalArray_origin_localAnalyticMajorant
    (P : Params) :
    Nonempty (LocalAnalyticMajorant
      (evenFirstOrderPrincipalArray P) firstOrderOrigin) :=
  exists_localAnalyticMajorant_of_analyticAt
    (analyticAt_evenFirstOrderPrincipalArray (firstOrderOrigin_inU P))

end

end StressTensor
