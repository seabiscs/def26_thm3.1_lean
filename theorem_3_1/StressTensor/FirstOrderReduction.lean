import StressTensor.QuasilinearNormalForm
import StressTensor.AxisFormulas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases

/-!
# A closed first-order reduction of the shifted auxiliary equation

Write `h = gamma + x` and introduce

* `v = h_x`, and
* `r = Gamma₂ = h - x + (y / 2) h_y`.

The coefficients of the resulting system depend only on `(y,v,r)`.  The
apparently missing variables `x`, `h`, and `h_y` cancel exactly between the
`h_yy` term and the derivative-free part of the shifted normal form.  This
file proves that cancellation algebraically and records the two-by-two
principal matrix of the reduced system.

No existence theorem is asserted here.  In particular, this reduction makes
the outstanding Cauchy--Kowalevskaya problem a first-order analytic system,
but it does not replace the required convergent-majorant argument.
-/

namespace StressTensor

noncomputable section

/-! ## Three-variable coefficient phase -/

/-- The reduced coefficient variables `(y,v,r)`, where `v=h_x` and
`r=Gamma₂`. -/
abbrev FirstOrderPhase := Fin 3 → ℝ

/-- Assemble a reduced phase point from its three named coordinates. -/
def firstOrderPhase (y v r : ℝ) : FirstOrderPhase := ![y, v, r]

@[simp] theorem firstOrderPhase_y (y v r : ℝ) :
    firstOrderPhase y v r 0 = y := by
  rfl

@[simp] theorem firstOrderPhase_v (y v r : ℝ) :
    firstOrderPhase y v r 1 = v := by
  rfl

@[simp] theorem firstOrderPhase_r (y v r : ℝ) :
    firstOrderPhase y v r 2 = r := by
  rfl

/-- `Gamma₁` expressed using only `(y,v,r)`. -/
def firstOrderGamma1 (w : FirstOrderPhase) : ℝ :=
  1 + (w 0) ^ 2 * (w 1 - 1)

/-- `Gamma₀` expressed using only `(y,v,r)`. -/
def firstOrderGamma0 (w : FirstOrderPhase) : ℝ :=
  2 * (w 1 - 1) + (w 0) ^ 2 * (w 1 - 1) ^ 2 + 4 * (w 2) ^ 2

/-- The scalar factor and its two derivatives at the reduced scalar point
`(y,Gamma₀(y,v,r))`. -/
def firstOrderScalarData (P : Params) (w : FirstOrderPhase) : ScalarData :=
  scalarDataAt P (w 0) (firstOrderGamma0 w)

/-- The noncharacteristic denominator in reduced variables. -/
def firstOrderCoeff0 (P : Params) (w : FirstOrderPhase) : ℝ :=
  (w 0) ^ 2 * (firstOrderScalarData P w).S +
    2 * firstOrderGamma1 w ^ 2 * (firstOrderScalarData P w).dSdd

/-- The quotient multiplying `y*r*v_y` in the first reduced equation. -/
def firstOrderCoeffA (P : Params) (w : FirstOrderPhase) : ℝ :=
  -(8 * firstOrderGamma1 w * (firstOrderScalarData P w).dSdd) /
    firstOrderCoeff0 P w

/-- The quotient multiplying `2*y*r_y` in the first reduced equation. -/
def firstOrderCoeffB (P : Params) (w : FirstOrderPhase) : ℝ :=
  -((firstOrderScalarData P w).S +
      8 * (w 2) ^ 2 * (firstOrderScalarData P w).dSdd) /
    firstOrderCoeff0 P w

/-- The remaining numerator after the `h_y` cancellation. -/
def firstOrderSourceNumerator (P : Params) (w : FirstOrderPhase) : ℝ :=
  4 * (w 0) ^ 2 * (w 2) * (firstOrderScalarData P w).dSdd * (w 1 - 1) ^ 2 +
    8 * firstOrderGamma1 w * (w 2) *
      (firstOrderScalarData P w).dSdd * (w 1 - 1) +
    2 * (w 0) * (w 2) * (firstOrderScalarData P w).dSdt +
    2 * (1 - 2 / P.p) * (firstOrderScalarData P w).S * (w 2)

/-- Right-hand side of the `v_x` equation, with `v_y` and `r_y` supplied as
independent jet coordinates. -/
def firstOrderVRate
    (P : Params) (w : FirstOrderPhase) (vy ry : ℝ) : ℝ :=
  (w 0) * (w 2) * firstOrderCoeffA P w * vy +
    2 * (w 0) * firstOrderCoeffB P w * ry -
      firstOrderSourceNumerator P w / firstOrderCoeff0 P w

/-- Right-hand side of the identity obtained by differentiating
`r = h - x + (y/2)h_y` in `x`. -/
def firstOrderRRate (w : FirstOrderPhase) (vy : ℝ) : ℝ :=
  (w 0) / 2 * vy + (w 1) - 1

/-- The derivative-free source in the first equation. -/
def firstOrderSourceRate (P : Params) (w : FirstOrderPhase) : ℝ :=
  -firstOrderSourceNumerator P w / firstOrderCoeff0 P w

/-! ## Relation to the shifted five-variable phase -/

/-- A canonical representative of `(y,v,r)` in shifted low-order
coordinates: `(x,y,h,h_x,h_y)=(0,y,r,v,0)`.  Its shifted `Gamma₂` is `r`,
and all reduced coefficients are independent of the three coordinates fixed
by this choice. -/
def firstOrderToShifted (w : FirstOrderPhase) : ShiftedPhase :=
  ![0, w 0, w 2, w 1, 0]

@[simp] theorem firstOrderToShifted_x (w : FirstOrderPhase) :
    firstOrderToShifted w 0 = 0 := by rfl

@[simp] theorem firstOrderToShifted_y (w : FirstOrderPhase) :
    firstOrderToShifted w 1 = w 0 := by rfl

@[simp] theorem firstOrderToShifted_h (w : FirstOrderPhase) :
    firstOrderToShifted w 2 = w 2 := by rfl

@[simp] theorem firstOrderToShifted_hx (w : FirstOrderPhase) :
    firstOrderToShifted w 3 = w 1 := by rfl

@[simp] theorem firstOrderToShifted_hy (w : FirstOrderPhase) :
    firstOrderToShifted w 4 = 0 := by rfl

/-- Membership in the analytic coefficient neighborhood, expressed through
the canonical shifted representative. -/
def FirstOrderPhaseInU (P : Params) (w : FirstOrderPhase) : Prop :=
  ShiftedPhaseInU P (firstOrderToShifted w)

/-- The canonical embedding is linear, hence analytic. -/
theorem analyticAt_firstOrderToShifted (w : FirstOrderPhase) :
    AnalyticAt ℝ firstOrderToShifted w := by
  have hc (i : Fin 3) : AnalyticAt ℝ (fun u : FirstOrderPhase => u i) w :=
    (ContinuousLinearMap.proj (R := ℝ) i).analyticAt w
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · simpa [firstOrderToShifted] using
      (analyticAt_const :
        AnalyticAt ℝ (fun _ : FirstOrderPhase => (0 : ℝ)) w)
  · simpa [firstOrderToShifted] using hc 0
  · simpa [firstOrderToShifted] using hc 2
  · simpa [firstOrderToShifted] using hc 1
  · simpa [firstOrderToShifted] using
      (analyticAt_const :
        AnalyticAt ℝ (fun _ : FirstOrderPhase => (0 : ℝ)) w)

@[simp] theorem shiftedGamma2_firstOrderToShifted (w : FirstOrderPhase) :
    shiftedGamma2 (firstOrderToShifted w) = w 2 := by
  simp [shiftedGamma2, firstOrderToShifted]

@[simp] theorem gamma2_firstOrderToShifted (w : FirstOrderPhase) :
    gamma2 ((firstOrderToShifted w) 1)
        (shiftedLowJet (firstOrderToShifted w)) = w 2 := by
  simp [gamma2, shiftedLowJet, shiftedJet]

@[simp] theorem gamma1_firstOrderToShifted (w : FirstOrderPhase) :
    gamma1 ((firstOrderToShifted w) 1)
        (shiftedLowJet (firstOrderToShifted w)) = firstOrderGamma1 w := by
  simp [gamma1, shiftedLowJet, shiftedJet, firstOrderToShifted,
    firstOrderGamma1]

@[simp] theorem gamma0_firstOrderToShifted (w : FirstOrderPhase) :
    gamma0 ((firstOrderToShifted w) 1)
        (shiftedLowJet (firstOrderToShifted w)) = firstOrderGamma0 w := by
  unfold gamma0
  rw [gamma2_firstOrderToShifted]
  simp [shiftedLowJet, shiftedJet, firstOrderGamma0]

@[simp] theorem shiftedScalarData_firstOrderToShifted
    (P : Params) (w : FirstOrderPhase) :
    shiftedScalarData P (firstOrderToShifted w) =
      firstOrderScalarData P w := by
  unfold shiftedScalarData scalarDataOfJet firstOrderScalarData
  rw [gamma0_firstOrderToShifted]
  simp

@[simp] theorem shiftedCoeff0_firstOrderToShifted
    (P : Params) (w : FirstOrderPhase) :
    coeff0 ((firstOrderToShifted w) 1)
        (shiftedLowJet (firstOrderToShifted w))
        (shiftedScalarData P (firstOrderToShifted w)) =
      firstOrderCoeff0 P w := by
  unfold coeff0 firstOrderCoeff0
  rw [shiftedScalarData_firstOrderToShifted,
    gamma1_firstOrderToShifted]
  simp

@[simp] theorem shiftedCoeffXYFactor_firstOrderToShifted
    (P : Params) (w : FirstOrderPhase) :
    shiftedCoeffXYFactor P (firstOrderToShifted w) =
      firstOrderCoeffA P w := by
  unfold shiftedCoeffXYFactor firstOrderCoeffA
  rw [shiftedCoeff0_firstOrderToShifted,
    shiftedScalarData_firstOrderToShifted, gamma1_firstOrderToShifted]

@[simp] theorem shiftedCoeffYYFactor_firstOrderToShifted
    (P : Params) (w : FirstOrderPhase) :
    shiftedCoeffYYFactor P (firstOrderToShifted w) =
      firstOrderCoeffB P w := by
  unfold shiftedCoeffYYFactor firstOrderCoeffB
  rw [shiftedCoeff0_firstOrderToShifted,
    shiftedScalarData_firstOrderToShifted,
    shiftedGamma2_firstOrderToShifted]

/-- The reduced source is the old shifted derivative-free term restricted to
the canonical three-variable slice. -/
@[simp] theorem shiftedConstant_firstOrderToShifted
    (P : Params) (w : FirstOrderPhase) :
    shiftedConstant P (firstOrderToShifted w) =
      firstOrderSourceRate P w := by
  unfold shiftedConstant quasilinearConstant
  rw [shiftedCoeff0_firstOrderToShifted]
  unfold lowerOrder
  rw [shiftedScalarData_firstOrderToShifted,
    gamma2_firstOrderToShifted,
    gamma1_firstOrderToShifted]
  simp only [shiftedLowJet, shiftedJet, firstOrderToShifted_hy,
    firstOrderToShifted_hx, firstOrderToShifted_y]
  unfold firstOrderSourceRate firstOrderSourceNumerator
  ring

/-! ## Analyticity of the reduced coefficients -/

/-- The three scalar-data coordinates are analytic on the reduced slice of
the manuscript's CK neighborhood. -/
theorem analyticAt_firstOrderScalarData
    {P : Params} {w : FirstOrderPhase} (hU : FirstOrderPhaseInU P w) :
    AnalyticAt ℝ (fun u : FirstOrderPhase => (firstOrderScalarData P u).S) w ∧
      AnalyticAt ℝ
        (fun u : FirstOrderPhase => (firstOrderScalarData P u).dSdt) w ∧
      AnalyticAt ℝ
        (fun u : FirstOrderPhase => (firstOrderScalarData P u).dSdd) w := by
  have he := analyticAt_firstOrderToShifted w
  have hs := analyticAt_shiftedScalarData hU
  constructor
  · apply (hs.1.comp he).congr
    exact Filter.Eventually.of_forall fun u => by
      simp [Function.comp_apply]
  constructor
  · apply (hs.2.1.comp he).congr
    exact Filter.Eventually.of_forall fun u => by
      simp [Function.comp_apply]
  · apply (hs.2.2.comp he).congr
    exact Filter.Eventually.of_forall fun u => by
      simp [Function.comp_apply]

/-- The reduced noncharacteristic coefficient is analytic. -/
theorem analyticAt_firstOrderCoeff0
    {P : Params} {w : FirstOrderPhase} (hU : FirstOrderPhaseInU P w) :
    AnalyticAt ℝ (firstOrderCoeff0 P) w := by
  have h := (analyticAt_shiftedCoeff0 hU).comp
    (analyticAt_firstOrderToShifted w)
  apply h.congr
  exact Filter.Eventually.of_forall fun u => by
    change coeff0 ((firstOrderToShifted u) 1)
      (shiftedLowJet (firstOrderToShifted u))
      (shiftedScalarData P (firstOrderToShifted u)) = firstOrderCoeff0 P u
    exact shiftedCoeff0_firstOrderToShifted P u

/-- The first principal quotient is analytic. -/
theorem analyticAt_firstOrderCoeffA
    {P : Params} {w : FirstOrderPhase} (hU : FirstOrderPhaseInU P w) :
    AnalyticAt ℝ (firstOrderCoeffA P) w := by
  have h := (analyticAt_shiftedCoeffXYFactor hU).comp
    (analyticAt_firstOrderToShifted w)
  apply h.congr
  exact Filter.Eventually.of_forall fun u => by
    simp [Function.comp_apply]

/-- The second principal quotient is analytic. -/
theorem analyticAt_firstOrderCoeffB
    {P : Params} {w : FirstOrderPhase} (hU : FirstOrderPhaseInU P w) :
    AnalyticAt ℝ (firstOrderCoeffB P) w := by
  have h := (analyticAt_shiftedCoeffYYFactor hU).comp
    (analyticAt_firstOrderToShifted w)
  apply h.congr
  exact Filter.Eventually.of_forall fun u => by
    simp [Function.comp_apply]

/-- The completely cancelled source is analytic. -/
theorem analyticAt_firstOrderSourceRate
    {P : Params} {w : FirstOrderPhase} (hU : FirstOrderPhaseInU P w) :
    AnalyticAt ℝ (firstOrderSourceRate P) w := by
  have h := (analyticAt_shiftedConstant hU).comp
    (analyticAt_firstOrderToShifted w)
  apply h.congr
  exact Filter.Eventually.of_forall fun u => by
    simp [Function.comp_apply]

/-- Noncharacteristic positivity is inherited by the reduced slice. -/
theorem firstOrderCoeff0_pos_of_inU
    {P : Params} {w : FirstOrderPhase} (hU : FirstOrderPhaseInU P w) :
    0 < firstOrderCoeff0 P w := by
  have h := coeff0_scalarDataOfJet_pos_of_inU P hU
  change 0 < coeff0 ((firstOrderToShifted w) 1)
    (shiftedLowJet (firstOrderToShifted w))
    (shiftedScalarData P (firstOrderToShifted w)) at h
  rw [shiftedCoeff0_firstOrderToShifted] at h
  exact h

/-- The canonical reduced origin lies in the coefficient neighborhood. -/
theorem firstOrderOrigin_inU (P : Params) :
    FirstOrderPhaseInU P 0 := by
  simpa [FirstOrderPhaseInU, firstOrderToShifted, ShiftedPhaseInU,
    shiftedLowJet, shiftedJet, initialJet] using
    (initialJet_inU P (y := 0) (by simpa using P.rho_pos))

/-! ## A jet realizing `(y,v,r)` -/

/-- A gamma-jet with prescribed `v=h_x`, `r=Gamma₂`, and the three
tangential derivatives used in the cancellation calculation. -/
def firstOrderJet (y v r hy vy hyy : ℝ) : Jet where
  val := r - y * hy / 2
  dx := v - 1
  dy := hy
  dxy := vy
  dyy := hyy

@[simp] theorem gamma1_firstOrderJet (y v r hy vy hyy : ℝ) :
    gamma1 y (firstOrderJet y v r hy vy hyy) =
      firstOrderGamma1 (firstOrderPhase y v r) := by
  simp [gamma1, firstOrderJet, firstOrderGamma1]

@[simp] theorem gamma2_firstOrderJet (y v r hy vy hyy : ℝ) :
    gamma2 y (firstOrderJet y v r hy vy hyy) = r := by
  simp [gamma2, firstOrderJet]

@[simp] theorem gamma0_firstOrderJet (y v r hy vy hyy : ℝ) :
    gamma0 y (firstOrderJet y v r hy vy hyy) =
      firstOrderGamma0 (firstOrderPhase y v r) := by
  unfold gamma0
  rw [gamma2_firstOrderJet]
  simp [firstOrderGamma0, firstOrderJet]

@[simp] theorem scalarDataOfJet_firstOrderJet
    (P : Params) (y v r hy vy hyy : ℝ) :
    scalarDataOfJet P y (firstOrderJet y v r hy vy hyy) =
      firstOrderScalarData P (firstOrderPhase y v r) := by
  simp [scalarDataOfJet, firstOrderScalarData]

@[simp] theorem coeff0_firstOrderJet
    (P : Params) (y v r hy vy hyy : ℝ) :
    coeff0 y (firstOrderJet y v r hy vy hyy)
        (firstOrderScalarData P (firstOrderPhase y v r)) =
      firstOrderCoeff0 P (firstOrderPhase y v r) := by
  simp [coeff0, firstOrderCoeff0]

/-! ## Exact cancellation and the closed system -/

/-- The tangential derivative identity for
`r = gamma + (y/2) gamma_y` in denominator-free form. -/
theorem firstOrder_tangential_compatibility (y hy hyy : ℝ) :
    y ^ 2 * hyy =
      2 * y * ((3 * hy + y * hyy) / 2) - 3 * y * hy := by
  ring

/-- Exact cancellation of every occurrence of `h`, `x`, and `h_y`.

The compatibility hypothesis is precisely
`2 y r_y = 3 y h_y + y² h_yy`, obtained by differentiating the definition
of `r` in the tangential variable and multiplying by `2y`.  The statement is
valid also at `y=0` and does not divide by `y`. -/
theorem normalForm_eq_firstOrderVRate
    (P : Params) (y v r hy vy hyy ry : ℝ)
    (hcompat : y ^ 2 * hyy = 2 * y * ry - 3 * y * hy) :
    normalForm P y (firstOrderJet y v r hy vy hyy)
        (firstOrderScalarData P (firstOrderPhase y v r)) =
      firstOrderVRate P (firstOrderPhase y v r) vy ry := by
  simp only [normalForm, coeff1, coeff2, lowerOrder]
  rw [gamma1_firstOrderJet, gamma2_firstOrderJet,
    coeff0_firstOrderJet]
  simp only [firstOrderJet, firstOrderVRate, firstOrderCoeffA,
    firstOrderCoeffB, firstOrderSourceNumerator,
    firstOrderPhase_y, firstOrderPhase_v, firstOrderPhase_r]
  have htop :
      y ^ 2 *
          ((firstOrderScalarData P (firstOrderPhase y v r)).S +
            8 * r ^ 2 *
              (firstOrderScalarData P (firstOrderPhase y v r)).dSdd) * hyy =
        (2 * y * ry - 3 * y * hy) *
          ((firstOrderScalarData P (firstOrderPhase y v r)).S +
            8 * r ^ 2 *
              (firstOrderScalarData P (firstOrderPhase y v r)).dSdd) := by
    calc
      _ = (y ^ 2 * hyy) *
          ((firstOrderScalarData P (firstOrderPhase y v r)).S +
            8 * r ^ 2 *
              (firstOrderScalarData P (firstOrderPhase y v r)).dSdd) := by ring
      _ = _ := by rw [hcompat]
  rw [htop]
  ring

/-- The cancellation theorem with `r_y` replaced by its natural jet-level
value `(3 h_y + y h_yy)/2`. -/
theorem normalForm_eq_firstOrderVRate_natural
    (P : Params) (y v r hy vy hyy : ℝ) :
    normalForm P y (firstOrderJet y v r hy vy hyy)
        (firstOrderScalarData P (firstOrderPhase y v r)) =
      firstOrderVRate P (firstOrderPhase y v r) vy
        ((3 * hy + y * hyy) / 2) := by
  apply normalForm_eq_firstOrderVRate
  exact firstOrder_tangential_compatibility y hy hyy

/-- With a nonzero leading coefficient, the original polynomial residual is
equivalent to the first equation of the reduced system. -/
theorem residualNormal_eq_zero_iff_firstOrderVRate
    (P : Params) (y v r hy vy hyy ry vxx : ℝ)
    (hcompat : y ^ 2 * hyy = 2 * y * ry - 3 * y * hy)
    (hcoeff0 : firstOrderCoeff0 P (firstOrderPhase y v r) ≠ 0) :
    residualNormal P y (firstOrderJet y v r hy vy hyy) vxx
        (firstOrderScalarData P (firstOrderPhase y v r)) = 0 ↔
      vxx = firstOrderVRate P (firstOrderPhase y v r) vy ry := by
  rw [residualNormal_eq_zero_iff P y
    (firstOrderJet y v r hy vy hyy) vxx
    (firstOrderScalarData P (firstOrderPhase y v r))]
  · rw [normalForm_eq_firstOrderVRate P y v r hy vy hyy ry hcompat]
  · simpa only [coeff0_firstOrderJet] using hcoeff0

/-- The second reduced equation is exactly the `x` derivative of
`r = h - x + (y/2)h_y`, written using `v=h_x` and `v_y=h_xy`. -/
theorem firstOrderRRate_eq (y v r vy : ℝ) :
    firstOrderRRate (firstOrderPhase y v r) vy =
      v - 1 + y * vy / 2 := by
  simp [firstOrderRRate]
  ring

/-! ## Principal matrix -/

/-- The matrix `N(y,v,r)` for which the reduced system has principal part
`y * N(y,v,r) * (v_y,r_y)`. -/
def firstOrderPrincipalCore
    (P : Params) (w : FirstOrderPhase) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(w 2) * firstOrderCoeffA P w, 2 * firstOrderCoeffB P w;
     (1 : ℝ) / 2,                    0]

/-- The first reduced rate is the first row of the principal matrix, times
`y`, plus its source. -/
theorem firstOrderVRate_eq_principalRow
    (P : Params) (w : FirstOrderPhase) (vy ry : ℝ) :
    firstOrderVRate P w vy ry =
      (w 0) *
          (firstOrderPrincipalCore P w 0 0 * vy +
            firstOrderPrincipalCore P w 0 1 * ry) -
        firstOrderSourceNumerator P w / firstOrderCoeff0 P w := by
  simp [firstOrderVRate, firstOrderPrincipalCore]
  ring

/-- The second reduced rate is the second row of the same principal matrix,
times `y`, plus the source `v-1`. -/
theorem firstOrderRRate_eq_principalRow
    (P : Params) (w : FirstOrderPhase) (vy ry : ℝ) :
    firstOrderRRate w vy =
      (w 0) *
          (firstOrderPrincipalCore P w 1 0 * vy +
            firstOrderPrincipalCore P w 1 1 * ry) +
        (w 1 - 1) := by
  simp [firstOrderRRate, firstOrderPrincipalCore]
  ring

/-- Trace of the reduced principal core. -/
@[simp] theorem firstOrderPrincipalCore_trace
    (P : Params) (w : FirstOrderPhase) :
    (firstOrderPrincipalCore P w).trace =
      (w 2) * firstOrderCoeffA P w := by
  rw [Matrix.trace_fin_two]
  simp [firstOrderPrincipalCore]

/-- Determinant of the reduced principal core. -/
@[simp] theorem firstOrderPrincipalCore_det
    (P : Params) (w : FirstOrderPhase) :
    (firstOrderPrincipalCore P w).det = -firstOrderCoeffB P w := by
  rw [Matrix.det_fin_two]
  simp [firstOrderPrincipalCore]
  ring

/-- The exact discriminant of the characteristic polynomial. -/
theorem firstOrderPrincipalCore_discriminant
    (P : Params) (w : FirstOrderPhase) :
    (firstOrderPrincipalCore P w).trace ^ 2 -
        4 * (firstOrderPrincipalCore P w).det =
      ((w 2) * firstOrderCoeffA P w) ^ 2 +
        4 * firstOrderCoeffB P w := by
  rw [firstOrderPrincipalCore_trace, firstOrderPrincipalCore_det]
  ring

/-! ## Even-coordinate (`t = y²`) principal form -/

/-- Principal core after the chain-rule substitution
`v_y=2y v_t`, `r_y=2y r_t`.  The transformed system has principal part
`y² * M * (v_t,r_t)`. -/
def evenFirstOrderPrincipalCore
    (P : Params) (w : FirstOrderPhase) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * (w 2) * firstOrderCoeffA P w, 4 * firstOrderCoeffB P w;
     (1 : ℝ),                              0]

/-- First transformed rate in the even coordinate `t=y²`. -/
def evenFirstOrderVRate
    (P : Params) (w : FirstOrderPhase) (vt rt : ℝ) : ℝ :=
  (w 0) ^ 2 *
      (evenFirstOrderPrincipalCore P w 0 0 * vt +
        evenFirstOrderPrincipalCore P w 0 1 * rt) +
    firstOrderSourceRate P w

/-- Second transformed rate in the even coordinate `t=y²`. -/
def evenFirstOrderRRate
    (P : Params) (w : FirstOrderPhase) (vt rt : ℝ) : ℝ :=
  (w 0) ^ 2 *
      (evenFirstOrderPrincipalCore P w 1 0 * vt +
        evenFirstOrderPrincipalCore P w 1 1 * rt) +
    (w 1 - 1)

/-- Exact first-row chain rule for `t=y²`. -/
theorem firstOrderVRate_even_chain
    (P : Params) (w : FirstOrderPhase) (vt rt : ℝ) :
    firstOrderVRate P w (2 * (w 0) * vt) (2 * (w 0) * rt) =
      evenFirstOrderVRate P w vt rt := by
  simp [firstOrderVRate, evenFirstOrderVRate,
    evenFirstOrderPrincipalCore, firstOrderSourceRate]
  ring

/-- Exact second-row chain rule for `t=y²`. -/
theorem firstOrderRRate_even_chain
    (P : Params) (w : FirstOrderPhase) (vt rt : ℝ) :
    firstOrderRRate w (2 * (w 0) * vt) =
      evenFirstOrderRRate P w vt rt := by
  simp [firstOrderRRate, evenFirstOrderRRate,
    evenFirstOrderPrincipalCore]
  ring

/-! ## Base point and elliptic principal type -/

/-- The origin in `(y,v,r)` variables. -/
def firstOrderOrigin : FirstOrderPhase := 0

@[simp] theorem firstOrderOrigin_apply (i : Fin 3) :
    firstOrderOrigin i = 0 := by
  rfl

/-- At the distinguished scalar point, `dS/dd = S/(2p)`. -/
theorem firstOrderScalarData_origin_dSdd
    (P : Params) :
    (firstOrderScalarData P firstOrderOrigin).dSdd =
      (firstOrderScalarData P firstOrderOrigin).S / (2 * P.p) := by
  simp only [firstOrderScalarData, scalarDataAt]
  have hgamma0 : firstOrderGamma0 firstOrderOrigin = -2 := by
    norm_num [firstOrderGamma0, firstOrderOrigin]
  rw [hgamma0]
  simp only [firstOrderOrigin_apply]
  rw [deriv_Stilde_d P 0 (-2) (by norm_num)]
  · simp [stildeDLogRate, Ctilde]
    field_simp [P.p_pos.ne', P.q_pos.ne']
  · simpa [Ctilde] using P.q_pos

/-- The scalar factor `S` is strictly positive at the reduced origin. -/
theorem firstOrderScalarData_origin_S_pos (P : Params) :
    0 < (firstOrderScalarData P firstOrderOrigin).S := by
  simp only [firstOrderScalarData, scalarDataAt]
  have hgamma0 : firstOrderGamma0 firstOrderOrigin = -2 := by
    norm_num [firstOrderGamma0, firstOrderOrigin]
  rw [hgamma0]
  apply Stilde_pos_of_pos P 0 (-2)
  · norm_num
  · simpa [Ctilde] using P.q_pos

/-- Exact value of the reduced noncharacteristic denominator at the origin. -/
theorem firstOrderCoeff0_origin (P : Params) :
    firstOrderCoeff0 P firstOrderOrigin =
      (firstOrderScalarData P firstOrderOrigin).S / P.p := by
  simp only [firstOrderCoeff0, firstOrderOrigin_apply]
  rw [firstOrderScalarData_origin_dSdd]
  simp [firstOrderGamma1, firstOrderOrigin]
  ring

theorem firstOrderCoeff0_origin_pos (P : Params) :
    0 < firstOrderCoeff0 P firstOrderOrigin := by
  rw [firstOrderCoeff0_origin]
  exact div_pos (firstOrderScalarData_origin_S_pos P) P.p_pos

/-- The mixed coefficient quotient has the particularly simple base value
`-4`. -/
@[simp] theorem firstOrderCoeffA_origin (P : Params) :
    firstOrderCoeffA P firstOrderOrigin = -4 := by
  rw [firstOrderCoeffA, firstOrderScalarData_origin_dSdd,
    firstOrderCoeff0_origin]
  have hS := (firstOrderScalarData_origin_S_pos P).ne'
  field_simp [hS, P.p_pos.ne']
  norm_num [firstOrderGamma1, firstOrderOrigin]

/-- The pure tangential coefficient quotient has base value `-p`. -/
@[simp] theorem firstOrderCoeffB_origin (P : Params) :
    firstOrderCoeffB P firstOrderOrigin = -P.p := by
  rw [firstOrderCoeffB, firstOrderCoeff0_origin]
  have hS := (firstOrderScalarData_origin_S_pos P).ne'
  simp only [firstOrderOrigin_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero]
  field_simp [hS, P.p_pos.ne']
  ring

/-- The principal core at the base point.  The actual spatial principal
matrix is `y` times this matrix. -/
theorem firstOrderPrincipalCore_origin (P : Params) :
    firstOrderPrincipalCore P firstOrderOrigin =
      !![(0 : ℝ), -2 * P.p; (1 : ℝ) / 2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstOrderPrincipalCore]

/-- Base matrix for the `t=y²` Fuchsian form. -/
theorem evenFirstOrderPrincipalCore_origin (P : Params) :
    evenFirstOrderPrincipalCore P firstOrderOrigin =
      !![(0 : ℝ), -4 * P.p; (1 : ℝ), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [evenFirstOrderPrincipalCore]

/-- The square of the even-coordinate base matrix is `-4p` times the
identity. -/
theorem evenFirstOrderPrincipalCore_origin_sq (P : Params) :
    evenFirstOrderPrincipalCore P firstOrderOrigin *
        evenFirstOrderPrincipalCore P firstOrderOrigin =
      (-4 * P.p) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [evenFirstOrderPrincipalCore_origin]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The base principal core has trace zero. -/
@[simp] theorem firstOrderPrincipalCore_origin_trace (P : Params) :
    (firstOrderPrincipalCore P firstOrderOrigin).trace = 0 := by
  rw [Matrix.trace_fin_two, firstOrderPrincipalCore_origin]
  norm_num

/-- The base principal core has determinant `p`. -/
@[simp] theorem firstOrderPrincipalCore_origin_det (P : Params) :
    (firstOrderPrincipalCore P firstOrderOrigin).det = P.p := by
  rw [Matrix.det_fin_two, firstOrderPrincipalCore_origin]
  norm_num
  ring

/-- The discriminant `trace²-4 det` is `-4p`. -/
theorem firstOrderPrincipalCore_origin_discriminant (P : Params) :
    (firstOrderPrincipalCore P firstOrderOrigin).trace ^ 2 -
        4 * (firstOrderPrincipalCore P firstOrderOrigin).det = -4 * P.p := by
  rw [firstOrderPrincipalCore_origin_trace, firstOrderPrincipalCore_origin_det]
  ring

/-- The base discriminant is strictly negative. -/
theorem firstOrderPrincipalCore_origin_discriminant_neg (P : Params) :
    (firstOrderPrincipalCore P firstOrderOrigin).trace ^ 2 -
        4 * (firstOrderPrincipalCore P firstOrderOrigin).det < 0 := by
  rw [firstOrderPrincipalCore_origin_discriminant]
  nlinarith [P.p_pos]

/-- The base characteristic polynomial, evaluated at a real scalar, is
`lambda²+p`. -/
theorem firstOrderPrincipalCore_origin_characteristic
    (P : Params) (lambda : ℝ) :
    lambda ^ 2 -
        (firstOrderPrincipalCore P firstOrderOrigin).trace * lambda +
        (firstOrderPrincipalCore P firstOrderOrigin).det =
      lambda ^ 2 + P.p := by
  rw [firstOrderPrincipalCore_origin_trace, firstOrderPrincipalCore_origin_det]
  ring

/-- Consequently the base principal core has no real characteristic root.
Equivalently, its two characteristic speeds are a nonreal conjugate pair. -/
theorem firstOrderPrincipalCore_origin_no_real_characteristic
    (P : Params) (lambda : ℝ) :
    0 < lambda ^ 2 -
        (firstOrderPrincipalCore P firstOrderOrigin).trace * lambda +
        (firstOrderPrincipalCore P firstOrderOrigin).det := by
  rw [firstOrderPrincipalCore_origin_characteristic]
  nlinarith [sq_nonneg lambda, P.p_pos]

/-- A useful matrix form of the same elliptic fact: the square of the base
principal core is `-p` times the identity. -/
theorem firstOrderPrincipalCore_origin_sq (P : Params) :
    firstOrderPrincipalCore P firstOrderOrigin *
        firstOrderPrincipalCore P firstOrderOrigin =
      (-P.p) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [firstOrderPrincipalCore_origin]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

end

end StressTensor
