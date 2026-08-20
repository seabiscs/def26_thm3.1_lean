import StressTensor.CKAnalyticCompetitorRecurrence
import StressTensor.CKFirstOrderVectorRHS
import StressTensor.FirstOrderReconstruction

/-!
# The actual stress equation supplies the analytic coefficient recurrence

This file closes the PDE-facing side of analytic competitor uniqueness.  It
turns the scalar auxiliary equation into the vector Fréchet-derivative
identity required by `CKAnalyticCompetitorRecurrence`, first for a germ and
then for an `IsCKSolution` on a centered reconstruction box.
-/

namespace StressTensor
namespace CKAnalyticCompetitorPDE

open CKFirstOrderFormalSystem CKPolarUniqueness
  CKAnalyticCompetitorRecurrence

noncomputable section

/-! ## Pointwise vector form -/

/-- At an analytic point where the noncharacteristic coefficient is nonzero,
the scalar auxiliary equation is exactly the vector reduced equation. -/
theorem fderiv_actualFirstOrderState_xDirection_eq_actualReducedRHS
    (P : Params) {gamma : ℝ → ℝ → ℝ} {z : Domain}
    (hgamma : AnalyticAt ℝ (uncurried gamma) z)
    (hcoeff0 : firstOrderCoeff0 P
      (firstOrderFieldPhase gamma z.1 z.2) ≠ 0)
    (haux : auxiliaryEquationAt P gamma z.1 z.2) :
    fderiv ℝ (actualFirstOrderState gamma) z xDirection =
      actualReducedRHS (firstOrderPrincipalArray P)
        (firstOrderSourceVector P) (actualFirstOrderState gamma) z := by
  rcases z with ⟨x, y⟩
  have hU : DifferentiableAt ℝ (actualFirstOrderState gamma) (x, y) :=
    (analyticAt_actualFirstOrderState hgamma).differentiableAt
  have hsys : FirstOrderSystemAt P gamma x y :=
    firstOrderSystemAt_of_auxiliaryEquationAt P
      (gammaDifferentialDataAt_of_analyticAt hgamma) hcoeff0 haux
  change fderiv ℝ (actualFirstOrderState gamma) (x, y) (1, 0) = _
  rw [fderiv_apply_xDirection_eq hU]
  unfold actualReducedRHS actualPhase
  change
    (fun i => deriv (fun xi => actualFirstOrderState gamma (xi, y) i) x) =
      Matrix.mulVec
          (firstOrderPrincipalArray P (firstOrderFieldPhase gamma x y))
          (y • fderiv ℝ (actualFirstOrderState gamma) (x, y) (0, 1)) +
        firstOrderSourceVector P (firstOrderFieldPhase gamma x y)
  rw [fderiv_apply_yDirection_eq hU]
  let w : FirstOrderPhase := firstOrderFieldPhase gamma x y
  let d : FirstOrderState :=
    fun i => deriv (fun eta => actualFirstOrderState gamma (x, eta) i) y
  calc
    (fun i => deriv (fun xi => actualFirstOrderState gamma (xi, y) i) x) =
        ![firstOrderVRate P w (d 0) (d 1),
          firstOrderRRate w (d 0)] := by
      funext i
      fin_cases i
      · simpa [w, d] using hsys.1
      · simpa [w, d] using hsys.2
    _ = Matrix.mulVec (firstOrderPrincipalArray P w) ((w 0) • d) +
          firstOrderSourceVector P w :=
      (firstOrder_vector_rhs_eq P w d).symm
    _ = Matrix.mulVec
          (firstOrderPrincipalArray P (firstOrderFieldPhase gamma x y))
          (y • fun i =>
            deriv (fun eta => actualFirstOrderState gamma (x, eta) i) y) +
        firstOrderSourceVector P (firstOrderFieldPhase gamma x y) := by
      rfl

/-! ## A neighborhood of the origin -/

/-- Analyticity, the auxiliary equation near the origin, and positive-radius
Cauchy data imply the local vector PDE consumed by the recurrence bridge.
Noncharacteristicity is not assumed separately: continuity propagates the
strictly positive origin value of `firstOrderCoeff0`. -/
theorem eventuallyEq_actualFirstOrderState_reducedPDE_of_analyticAt
    (P : Params) {gamma : ℝ → ℝ → ℝ} {radius : ℝ}
    (hgamma : AnalyticAt ℝ (uncurried gamma) 0)
    (hdata : HasCauchyDataOn gamma radius) (hradius : 0 < radius)
    (haux : ∀ᶠ z in nhds (0 : Domain),
      auxiliaryEquationAt P gamma z.1 z.2) :
    (fun z => fderiv ℝ (actualFirstOrderState gamma) z xDirection) =ᶠ[nhds 0]
      actualReducedRHS (firstOrderPrincipalArray P)
        (firstOrderSourceVector P) (actualFirstOrderState gamma) := by
  let phase : Domain → FirstOrderPhase :=
    fun z => firstOrderFieldPhase gamma z.1 z.2
  have hU0 : actualFirstOrderState gamma 0 = 0 := by
    apply actualFirstOrderState_zero_on_cauchyAxis_of_hasCauchyDataOn hdata
    simpa only [abs_zero] using hradius
  have hphase0 : phase 0 = firstOrderOrigin := by
    change firstOrderPhase 0
      (actualFirstOrderState gamma 0 0)
      (actualFirstOrderState gamma 0 1) = firstOrderOrigin
    rw [hU0]
    simp [firstOrderPhase, firstOrderOrigin]
  have hphase : AnalyticAt ℝ phase 0 := by
    rcases analyticAt_actualFirstOrderState hgamma with ⟨u, hu⟩
    have hp := (hasFPowerSeriesAt_phaseSeries hu).analyticAt
    simpa only [phase, firstOrderFieldPhase, actualFirstOrderState_zero,
      actualFirstOrderState_one] using hp
  have hcoeffAnalytic : AnalyticAt ℝ
      (fun z => firstOrderCoeff0 P (phase z)) 0 := by
    have hc : AnalyticAt ℝ (firstOrderCoeff0 P) (phase 0) := by
      rw [hphase0]
      exact analyticAt_firstOrderCoeff0 (firstOrderOrigin_inU P)
    simpa only [Function.comp_def] using hc.comp hphase
  have hcoeffOrigin : firstOrderCoeff0 P (phase 0) ≠ 0 := by
    rw [hphase0]
    exact (firstOrderCoeff0_origin_pos P).ne'
  have hcoeff : ∀ᶠ z in nhds (0 : Domain),
      firstOrderCoeff0 P (phase z) ≠ 0 :=
    hcoeffAnalytic.continuousAt.eventually_ne hcoeffOrigin
  have hanalytic : ∀ᶠ z in nhds (0 : Domain),
      AnalyticAt ℝ (uncurried gamma) z := hgamma.eventually_analyticAt
  filter_upwards [hanalytic, hcoeff, haux] with z hz hc ha
  exact fderiv_actualFirstOrderState_xDirection_eq_actualReducedRHS
    P hz hc ha

/-! ## Actual CK solutions -/

/-- Every analytic CK solution on a positive centered reconstruction box
satisfies the required vector PDE in a neighborhood of the origin. -/
theorem IsCKSolution.eventuallyEq_actualFirstOrderState_reducedPDE
    (P : Params) {gamma : ℝ → ℝ → ℝ} {rx ry : ℝ}
    (hsol : IsCKSolution P (reconstructionBox rx ry) ry gamma)
    (hrx : 0 < rx) (hry : 0 < ry) :
    (fun z => fderiv ℝ (actualFirstOrderState gamma) z xDirection) =ᶠ[nhds 0]
      actualReducedRHS (firstOrderPrincipalArray P)
        (firstOrderSourceVector P) (actualFirstOrderState gamma) := by
  have horigin : (0 : Domain) ∈ reconstructionBox rx ry := by
    exact mem_reconstructionBox.2 ⟨by simpa using hrx, by simpa using hry⟩
  have hopen : IsOpen (reconstructionBox rx ry) := by
    exact isOpen_Ioo.prod isOpen_Ioo
  have hbox : reconstructionBox rx ry ∈ nhds (0 : Domain) :=
    hopen.mem_nhds horigin
  have haux : ∀ᶠ z in nhds (0 : Domain),
      auxiliaryEquationAt P gamma z.1 z.2 := by
    filter_upwards [hbox] with z hz
    exact hsol.2.1 hz
  exact eventuallyEq_actualFirstOrderState_reducedPDE_of_analyticAt P
    (hsol.1 0 horigin) hsol.2.2 hry haux

/-- Consequently, every FMS of the actual analytic state of a CK solution
satisfies the equation-specific reduced coefficient recurrence. -/
theorem IsCKSolution.satisfiesReducedArrayRecurrence
    (P : Params) {gamma : ℝ → ℝ → ℝ} {rx ry : ℝ}
    (hsol : IsCKSolution P (reconstructionBox rx ry) ry gamma)
    (hrx : 0 < rx) (hry : 0 < ry)
    {u : StateSeries}
    (hu : HasFPowerSeriesAt (actualFirstOrderState gamma) u 0) :
    SatisfiesReducedArrayRecurrence
      (firstOrderPrincipalOriginMajorant P).series
      (firstOrderSourceOriginMajorant P).series
      (polarCoefficientArray u) := by
  exact actualFirstOrderState_satisfiesReducedArrayRecurrence
    P hu hsol.2.2 hry
      (IsCKSolution.eventuallyEq_actualFirstOrderState_reducedPDE
        P hsol hrx hry)

/-- A convergent realization of the formal reduced coefficients has the same
component jets as every actual analytic CK solution on the box. -/
theorem IsCKSolution.actualFirstOrderState_componentJetsAgree
    (P : Params) {gamma : ℝ → ℝ → ℝ} {rx ry : ℝ}
    (hsol : IsCKSolution P (reconstructionBox rx ry) ry gamma)
    (hrx : 0 < rx) (hry : 0 < ry)
    {V : Domain → FirstOrderState}
    (hV : HasFPowerSeriesAt V
      (stateBivariateFMS (firstOrderFormalCoefficients P)) 0) :
    FirstOrderComponentJetsAgreeAt
      (actualFirstOrderState gamma) V 0 := by
  have horigin : (0 : Domain) ∈ reconstructionBox rx ry := by
    exact mem_reconstructionBox.2 ⟨by simpa using hrx, by simpa using hry⟩
  apply actualFirstOrderState_componentJetsAgree_firstOrderFormalCoefficients
    P (hsol.1 0 horigin) hsol.2.2 hry
  · intro p hp
    exact IsCKSolution.satisfiesReducedArrayRecurrence
      P hsol hrx hry hp
  · exact hV

end

end CKAnalyticCompetitorPDE
end StressTensor
