import StressTensor.FirstOrderReduction

/-!
# Actual-function bridge for the first-order reduction

`FirstOrderReduction` proves the reduction at the level of algebraic jets.
This file identifies those jets with derivatives of actual functions.  For
`h = gamma + x`, set

* `v = h_x = gamma_x + 1`, and
* `r = gamma + (y/2) gamma_y = Gamma₂[gamma]`.

Under the six first/second derivative witnesses packaged by
`GammaDifferentialDataAt`, the original auxiliary equation is equivalent,
where the leading coefficient is nonzero, to the two actual first-order
equations for `(v,r)`.
-/

namespace StressTensor

noncomputable section

/-! ## Actual reduced fields -/

/-- The zero-Cauchy-data shift `h=gamma+x`. -/
def shiftedField (gamma : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  gamma x y + x

/-- The first reduced unknown `v=h_x`, written as `gamma_x+1` so that its
relation to the original jet is definitionally transparent. -/
def firstOrderVField (gamma : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialX gamma x y + 1

/-- The second reduced unknown `r=Gamma₂[gamma]`. -/
def firstOrderRField (gamma : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  gamma2Field gamma x y

/-- The actual reduced coefficient phase `(y,v,r)`. -/
def firstOrderFieldPhase
    (gamma : ℝ → ℝ → ℝ) (x y : ℝ) : FirstOrderPhase :=
  firstOrderPhase y (firstOrderVField gamma x y)
    (firstOrderRField gamma x y)

/-- The derivative of the shifted field in `x` is the reduced field `v`. -/
theorem hasDerivAt_shiftedField_x
    {gamma : ℝ → ℝ → ℝ} {x y : ℝ}
    (hx : HasDerivAt (fun xi => gamma xi y) (partialX gamma x y) x) :
    HasDerivAt (fun xi => shiftedField gamma xi y)
      (firstOrderVField gamma x y) x := by
  have hraw := hx.add (hasDerivAt_id' x)
  apply hraw.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun _ => rfl

/-- In particular, Mathlib's total `partialX` agrees with `v` whenever the
displayed derivative exists. -/
theorem partialX_shiftedField_eq_firstOrderVField
    {gamma : ℝ → ℝ → ℝ} {x y : ℝ}
    (hx : HasDerivAt (fun xi => gamma xi y) (partialX gamma x y) x) :
    partialX (shiftedField gamma) x y = firstOrderVField gamma x y := by
  exact (hasDerivAt_shiftedField_x hx).deriv

@[simp] theorem firstOrderRField_eq
    (gamma : ℝ → ℝ → ℝ) (x y : ℝ) :
    firstOrderRField gamma x y =
      gamma x y + y * partialY gamma x y / 2 := by
  rfl

/-- The actual original jet is exactly the canonical reduced jet. -/
theorem jetOf_eq_firstOrderJet
    (gamma : ℝ → ℝ → ℝ) (x y : ℝ) :
    jetOf gamma x y =
      firstOrderJet y (firstOrderVField gamma x y)
        (firstOrderRField gamma x y) (partialY gamma x y)
        (partialXY gamma x y) (partialYY gamma x y) := by
  simp [jetOf, firstOrderJet, firstOrderVField, firstOrderRField,
    gamma2Field, gamma2]

/-- Consequently the scalar data computed from the actual jet are exactly
the scalar data of the reduced three-variable phase. -/
theorem scalarDataOfJet_eq_firstOrderScalarData
    (P : Params) (gamma : ℝ → ℝ → ℝ) (x y : ℝ) :
    scalarDataOfJet P y (jetOf gamma x y) =
      firstOrderScalarData P (firstOrderFieldPhase gamma x y) := by
  rw [jetOf_eq_firstOrderJet]
  simp [firstOrderFieldPhase]

/-- The actual leading coefficient is the reduced leading coefficient. -/
theorem coeff0_field_eq_firstOrderCoeff0
    (P : Params) (gamma : ℝ → ℝ → ℝ) (x y : ℝ) :
    coeff0 y (jetOf gamma x y) (scalarDataOfJet P y (jetOf gamma x y)) =
      firstOrderCoeff0 P (firstOrderFieldPhase gamma x y) := by
  rw [jetOf_eq_firstOrderJet]
  simp [firstOrderFieldPhase]

/-! ## Derivatives of the actual reduced fields -/

theorem hasDerivAt_firstOrderVField_x
    {gamma : ℝ → ℝ → ℝ} {x y : ℝ}
    (hxx : HasDerivAt (fun xi => partialX gamma xi y)
      (partialXX gamma x y) x) :
    HasDerivAt (fun xi => firstOrderVField gamma xi y)
      (partialXX gamma x y) x := by
  have hraw := hxx.add (hasDerivAt_const x 1)
  have hraw' : HasDerivAt
      ((fun xi => partialX gamma xi y) + fun _ => (1 : ℝ))
      (partialXX gamma x y) x := hraw.congr_deriv (by simp)
  apply hraw'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun _ => rfl

theorem hasDerivAt_firstOrderVField_y
    {gamma : ℝ → ℝ → ℝ} {x y : ℝ}
    (hxy : HasDerivAt (fun eta => partialX gamma x eta)
      (partialXY gamma x y) y) :
    HasDerivAt (fun eta => firstOrderVField gamma x eta)
      (partialXY gamma x y) y := by
  have hraw := hxy.add (hasDerivAt_const y 1)
  have hraw' : HasDerivAt
      ((fun eta => partialX gamma x eta) + fun _ => (1 : ℝ))
      (partialXY gamma x y) y := hraw.congr_deriv (by simp)
  apply hraw'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun _ => rfl

theorem hasDerivAt_firstOrderRField_x
    {gamma : ℝ → ℝ → ℝ} {x y : ℝ}
    (hx : HasDerivAt (fun xi => gamma xi y) (partialX gamma x y) x)
    (hyx : HasDerivAt (fun xi => partialY gamma xi y)
      (partialXY gamma x y) x) :
    HasDerivAt (fun xi => firstOrderRField gamma xi y)
      (partialX gamma x y + y * partialXY gamma x y / 2) x := by
  simpa [firstOrderRField] using hasDerivAt_gamma2Field_x hx hyx

theorem hasDerivAt_firstOrderRField_y
    {gamma : ℝ → ℝ → ℝ} {x y : ℝ}
    (hy : HasDerivAt (gamma x) (partialY gamma x y) y)
    (hyy : HasDerivAt (fun eta => partialY gamma x eta)
      (partialYY gamma x y) y) :
    HasDerivAt (fun eta => firstOrderRField gamma x eta)
      ((3 * partialY gamma x y + y * partialYY gamma x y) / 2) y := by
  simpa [firstOrderRField] using hasDerivAt_gamma2Field_y hy hyy

/-! ## The actual first-order system -/

/-- Pointwise meaning of the two first-order equations for the actual fields
`v` and `r`. -/
def FirstOrderSystemAt
    (P : Params) (gamma : ℝ → ℝ → ℝ) (x y : ℝ) : Prop :=
  deriv (fun xi => firstOrderVField gamma xi y) x =
      firstOrderVRate P (firstOrderFieldPhase gamma x y)
        (deriv (fun eta => firstOrderVField gamma x eta) y)
        (deriv (fun eta => firstOrderRField gamma x eta) y) ∧
    deriv (fun xi => firstOrderRField gamma xi y) x =
      firstOrderRRate (firstOrderFieldPhase gamma x y)
        (deriv (fun eta => firstOrderVField gamma x eta) y)

/-- The auxiliary equation implies both actual reduced equations. -/
theorem firstOrderSystemAt_of_auxiliaryEquationAt
    (P : Params) {gamma : ℝ → ℝ → ℝ} {x y : ℝ}
    (hreg : GammaDifferentialDataAt gamma x y)
    (hcoeff0 : firstOrderCoeff0 P (firstOrderFieldPhase gamma x y) ≠ 0)
    (haux : auxiliaryEquationAt P gamma x y) :
    FirstOrderSystemAt P gamma x y := by
  have hvx := hasDerivAt_firstOrderVField_x hreg.dxx
  have hvy := hasDerivAt_firstOrderVField_y hreg.dxy
  have hrx := hasDerivAt_firstOrderRField_x hreg.dx hreg.dyx
  have hry := hasDerivAt_firstOrderRField_y hreg.dy hreg.dyy
  have hcoeff0' :
      coeff0 y (jetOf gamma x y)
          (scalarDataOfJet P y (jetOf gamma x y)) ≠ 0 := by
    rw [coeff0_field_eq_firstOrderCoeff0]
    exact hcoeff0
  have hnormal :=
    (auxiliaryEquation_iff_normalForm P gamma x y hcoeff0').mp haux
  have hnormalReduced :
      partialXX gamma x y =
        firstOrderVRate P (firstOrderFieldPhase gamma x y)
          (partialXY gamma x y)
          ((3 * partialY gamma x y + y * partialYY gamma x y) / 2) := by
    calc
      partialXX gamma x y =
          normalForm P y (jetOf gamma x y)
            (scalarDataOfJet P y (jetOf gamma x y)) := hnormal
      _ = normalForm P y
          (firstOrderJet y (firstOrderVField gamma x y)
            (firstOrderRField gamma x y) (partialY gamma x y)
            (partialXY gamma x y) (partialYY gamma x y))
          (firstOrderScalarData P (firstOrderFieldPhase gamma x y)) := by
            rw [jetOf_eq_firstOrderJet]
            simp [firstOrderFieldPhase]
      _ = _ := by
        simpa [firstOrderFieldPhase] using
          normalForm_eq_firstOrderVRate_natural P y
            (firstOrderVField gamma x y) (firstOrderRField gamma x y)
            (partialY gamma x y) (partialXY gamma x y)
            (partialYY gamma x y)
  constructor
  · rw [hvx.deriv, hvy.deriv, hry.deriv]
    exact hnormalReduced
  · rw [hrx.deriv, hvy.deriv]
    simp [firstOrderRRate, firstOrderFieldPhase, firstOrderVField]
    ring

/-- Conversely, the first-order system implies the original auxiliary
equation.  The second equation is kinematic; the first one plus the
tangential derivative identities recovers the normal form. -/
theorem auxiliaryEquationAt_of_firstOrderSystemAt
    (P : Params) {gamma : ℝ → ℝ → ℝ} {x y : ℝ}
    (hreg : GammaDifferentialDataAt gamma x y)
    (hcoeff0 : firstOrderCoeff0 P (firstOrderFieldPhase gamma x y) ≠ 0)
    (hsys : FirstOrderSystemAt P gamma x y) :
    auxiliaryEquationAt P gamma x y := by
  have hvx := hasDerivAt_firstOrderVField_x hreg.dxx
  have hvy := hasDerivAt_firstOrderVField_y hreg.dxy
  have hry := hasDerivAt_firstOrderRField_y hreg.dy hreg.dyy
  have hfirst := hsys.1
  rw [hvx.deriv, hvy.deriv, hry.deriv] at hfirst
  have hnormalReduced :
      partialXX gamma x y =
        normalForm P y
          (firstOrderJet y (firstOrderVField gamma x y)
            (firstOrderRField gamma x y) (partialY gamma x y)
            (partialXY gamma x y) (partialYY gamma x y))
          (firstOrderScalarData P (firstOrderFieldPhase gamma x y)) := by
    calc
      partialXX gamma x y =
          firstOrderVRate P (firstOrderFieldPhase gamma x y)
            (partialXY gamma x y)
            ((3 * partialY gamma x y + y * partialYY gamma x y) / 2) :=
        hfirst
      _ = normalForm P y
          (firstOrderJet y (firstOrderVField gamma x y)
            (firstOrderRField gamma x y) (partialY gamma x y)
            (partialXY gamma x y) (partialYY gamma x y))
          (firstOrderScalarData P (firstOrderFieldPhase gamma x y)) := by
        simpa [firstOrderFieldPhase] using
          (normalForm_eq_firstOrderVRate_natural P y
            (firstOrderVField gamma x y) (firstOrderRField gamma x y)
            (partialY gamma x y) (partialXY gamma x y)
            (partialYY gamma x y)).symm
  have hcoeff0' :
      coeff0 y (jetOf gamma x y)
          (scalarDataOfJet P y (jetOf gamma x y)) ≠ 0 := by
    rw [coeff0_field_eq_firstOrderCoeff0]
    exact hcoeff0
  apply (auxiliaryEquation_iff_normalForm P gamma x y hcoeff0').2
  calc
    partialXX gamma x y =
        normalForm P y
          (firstOrderJet y (firstOrderVField gamma x y)
            (firstOrderRField gamma x y) (partialY gamma x y)
            (partialXY gamma x y) (partialYY gamma x y))
          (firstOrderScalarData P (firstOrderFieldPhase gamma x y)) :=
      hnormalReduced
    _ = normalForm P y (jetOf gamma x y)
        (scalarDataOfJet P y (jetOf gamma x y)) := by
      rw [jetOf_eq_firstOrderJet]
      simp [firstOrderFieldPhase]

/-- Pointwise equivalence of the actual auxiliary PDE and the closed
first-order system under the regularity supplied, in particular, by
analyticity. -/
theorem firstOrderSystemAt_iff_auxiliaryEquationAt
    (P : Params) {gamma : ℝ → ℝ → ℝ} {x y : ℝ}
    (hreg : GammaDifferentialDataAt gamma x y)
    (hcoeff0 : firstOrderCoeff0 P (firstOrderFieldPhase gamma x y) ≠ 0) :
    FirstOrderSystemAt P gamma x y ↔ auxiliaryEquationAt P gamma x y := by
  constructor
  · exact auxiliaryEquationAt_of_firstOrderSystemAt P hreg hcoeff0
  · exact firstOrderSystemAt_of_auxiliaryEquationAt P hreg hcoeff0

/-- Analyticity of `gamma` supplies all hypotheses of the preceding
equivalence automatically. -/
theorem firstOrderSystemAt_iff_auxiliaryEquationAt_of_analyticAt
    (P : Params) {gamma : ℝ → ℝ → ℝ} {x y : ℝ}
    (hgamma : AnalyticAt ℝ (uncurried gamma) (x, y))
    (hcoeff0 : firstOrderCoeff0 P (firstOrderFieldPhase gamma x y) ≠ 0) :
    FirstOrderSystemAt P gamma x y ↔ auxiliaryEquationAt P gamma x y :=
  firstOrderSystemAt_iff_auxiliaryEquationAt P
    (gammaDifferentialDataAt_of_analyticAt hgamma) hcoeff0

end

end StressTensor
