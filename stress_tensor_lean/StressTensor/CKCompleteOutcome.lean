import StressTensor.CKAnalyticCompetitorPDE
import StressTensor.CKFirstOrderCompleteConvergence
import StressTensor.CKFirstOrderSeriesEvaluation
import StressTensor.CKLocalBox
import StressTensor.CKOutcomeAssembly

/-!
# Complete local analytic Cauchy--Kowalevskaya outcome

The unconditional normalized Nagumo bound is combined here with analytic
series evaluation, local noncharacteristicity, and analytic-competitor
uniqueness.  The result is an actual `CKOutcome` on a positive centered box,
with no remaining recurrence, convergence, or uniqueness hypothesis.
-/

namespace StressTensor
namespace CKCompleteOutcome

open CKFirstOrderFormalSystem CKVectorAnalyticEvaluation
  CKReducedSeriesRealization CKFirstOrderCompleteConvergence
  CKFirstOrderSeriesEvaluation CKAnalyticCompetitorRecurrence
  CKAnalyticCompetitorPDE CKLocalBox CKOutcomeAssembly

noncomputable section

/-- Positive centered radii together with the fully constructed local
analytic CK outcome on that box. -/
structure PositiveCKOutcomeData (P : Params) where
  rx : ℝ
  ry : ℝ
  rx_pos : 0 < rx
  ry_pos : 0 < ry
  outcome : CKOutcome P (reconstructionBox rx ry) ry

/-- The zero Cauchy row of the formal vector coefficients, in the component
layout consumed by series evaluation and reconstruction. -/
private theorem firstOrderSeriesComponents_zeroRow
    (P : Params) :
    ∀ i n, firstOrderSeriesComponents P i 0 n = 0 := by
  intro i n
  change firstOrderFormalCoefficients P 0 n i = 0
  rw [firstOrderFormalCoefficients_zero_x]
  rfl

/-- The evaluated formal phase is noncharacteristic throughout some
neighborhood of the origin. -/
private theorem eventually_firstOrderSeries_noncharacteristic
    (P : Params)
    {M sx sy : ℝ}
    (hgeom : VectorGeometricBound
      (firstOrderSeriesComponents P) M sx sy) :
    ∀ᶠ z : Domain in nhds 0,
      firstOrderCoeff0 P
        (reducedSeriesPhase (firstOrderSeriesComponents P) z.1 z.2) ≠ 0 := by
  let a := firstOrderSeriesComponents P
  have hU := hasFPowerSeriesAt_firstOrderSeriesState P hgeom
  have hU0 : firstOrderSeriesState P 0 = 0 :=
    firstOrderSeriesState_zero P hgeom
  have hphase0 : reducedSeriesPhase a 0 0 = firstOrderOrigin := by
    change firstOrderPhase 0
      (firstOrderSeriesState P 0 0)
      (firstOrderSeriesState P 0 1) = firstOrderOrigin
    rw [hU0]
    simp [firstOrderPhase, firstOrderOrigin]
  have hphase : AnalyticAt ℝ
      (fun z : Domain => reducedSeriesPhase a z.1 z.2) 0 := by
    have hp :=
      (hasFPowerSeriesAt_phaseSeries hU).analyticAt
    change AnalyticAt ℝ
      (fun z : Domain => reducedSeriesPhase a z.1 z.2) 0 at hp
    exact hp
  have hcoeffAnalytic : AnalyticAt ℝ
      (fun z : Domain =>
        firstOrderCoeff0 P (reducedSeriesPhase a z.1 z.2)) 0 := by
    have hc : AnalyticAt ℝ (firstOrderCoeff0 P)
        (reducedSeriesPhase a 0 0) := by
      rw [hphase0]
      exact analyticAt_firstOrderCoeff0 (firstOrderOrigin_inU P)
    simpa only [Function.comp_def] using
      hc.comp (f := fun z : Domain => reducedSeriesPhase a z.1 z.2) hphase
  have hcoeff0 :
      firstOrderCoeff0 P (reducedSeriesPhase a 0 0) ≠ 0 := by
    rw [hphase0]
    exact (firstOrderCoeff0_origin_pos P).ne'
  exact hcoeffAnalytic.continuousAt.eventually_ne hcoeff0

/-- Unconditional local analytic existence and uniqueness, with positive
radii retained for subsequent localization arguments. -/
theorem nonempty_positiveCKOutcomeData (P : Params) :
    Nonempty (PositiveCKOutcomeData P) := by
  let a := firstOrderSeriesComponents P
  let M := epsilon P
  let sx := 2 * evolutionRate P
  let sy := 2 * tangentialRate P
  have hgeom : VectorGeometricBound a M sx sy := by
    simpa only [a, M, sx, sy] using
      firstOrderFormalCoefficients_vectorGeometricBound P
  have hsx : 0 ≤ sx := by
    exact mul_nonneg (by norm_num) (evolutionRate_pos P).le
  have hsy : 0 ≤ sy := by
    exact mul_nonneg (by norm_num) (tangentialRate_pos P).le
  have hidEventually : ∀ᶠ z : Domain in nhds 0,
      ReducedSeriesIdentityAt P a z.1 z.2 := by
    simpa only [a] using
      eventually_reducedSeriesIdentityAt_firstOrderFormalCoefficients
        P hgeom
  have hnoncharEventually : ∀ᶠ z : Domain in nhds 0,
      firstOrderCoeff0 P (reducedSeriesPhase a z.1 z.2) ≠ 0 := by
    simpa only [a] using eventually_firstOrderSeries_noncharacteristic
      P hgeom
  let good : Set Domain := {z |
    ReducedSeriesIdentityAt P a z.1 z.2 ∧
      firstOrderCoeff0 P (reducedSeriesPhase a z.1 z.2) ≠ 0}
  have hgood : good ∈ nhds (0 : Domain) := by
    change ∀ᶠ z : Domain in nhds 0,
      ReducedSeriesIdentityAt P a z.1 z.2 ∧
        firstOrderCoeff0 P (reducedSeriesPhase a z.1 z.2) ≠ 0
    exact hidEventually.and hnoncharEventually
  obtain ⟨rx, ry, hrx, hry, hxrate, hyrate, hbox⟩ :=
    exists_convergenceBox_subset_of_mem_nhds_zero hsx hsy hgood
  have hrow : ∀ i n, a i 0 n = 0 := by
    simpa only [a] using firstOrderSeriesComponents_zeroRow P
  have hid : ∀ x y, |x| < rx → |y| < ry →
      ReducedSeriesIdentityAt P a x y := by
    intro x y hx hy
    have hz : (x, y) ∈ Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry :=
      ⟨abs_lt.mp hx, abs_lt.mp hy⟩
    exact (hbox hz).1
  have hnonchar : ∀ x y, |x| < rx → |y| < ry →
      firstOrderCoeff0 P (reducedSeriesPhase a x y) ≠ 0 := by
    intro x y hx hy
    have hz : (x, y) ∈ Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry :=
      ⟨abs_lt.mp hx, abs_lt.mp hy⟩
    exact (hbox hz).2
  let v : ℝ → ℝ → ℝ := fun x y => reducedSeriesField a x y 0
  let r : ℝ → ℝ → ℝ := fun x y => reducedSeriesField a x y 1
  have D : AnalyticFirstOrderReconstructionData v r rx ry := by
    simpa only [v, r] using
      analyticFirstOrderReconstructionData_of_reducedSeriesIdentityOn
        hgeom hrx hry hxrate hyrate hrow hid
  have horigin : (0 : Domain) ∈ reconstructionBox rx ry :=
    mem_reconstructionBox.2 ⟨by simpa using hrx, by simpa using hry⟩
  have hboxNhd : reconstructionBox rx ry ∈ nhds (0 : Domain) := by
    exact (isOpen_Ioo.prod isOpen_Ioo).mem_nhds horigin
  have hstate : firstOrderSeriesState P =ᶠ[nhds 0]
      actualFirstOrderState (reconstructedSeriesGamma a) := by
    filter_upwards [hboxNhd] with z hz
    rcases mem_reconstructionBox.mp hz with ⟨hx, hy⟩
    funext i
    fin_cases i
    · have hv := D.firstOrderVField_gamma hx hy
      change firstOrderSeriesState P z 0 =
        firstOrderVField (reconstructedSeriesGamma a) z.1 z.2
      calc
        firstOrderSeriesState P z 0 = v z.1 z.2 := rfl
        _ = firstOrderVField (reconstructedSeriesGamma a) z.1 z.2 := by
          simpa only [v, reconstructedSeriesGamma] using hv.symm
    · have hr := D.firstOrderRField_gamma hx hy
      change firstOrderSeriesState P z 1 =
        firstOrderRField (reconstructedSeriesGamma a) z.1 z.2
      calc
        firstOrderSeriesState P z 1 = r z.1 z.2 := rfl
        _ = firstOrderRField (reconstructedSeriesGamma a) z.1 z.2 := by
          simpa only [v, r, reconstructedSeriesGamma] using hr.symm
  have hseries : HasFPowerSeriesAt (firstOrderSeriesState P)
      (stateBivariateFMS (firstOrderFormalCoefficients P)) 0 :=
    hasFPowerSeriesAt_firstOrderSeriesState P hgeom
  have hreconstructed : HasFPowerSeriesAt
      (actualFirstOrderState (reconstructedSeriesGamma a))
      (stateBivariateFMS (firstOrderFormalCoefficients P)) 0 :=
    hseries.congr hstate
  have hdet : ∀ eta : ℝ → ℝ → ℝ,
      IsCKSolution P (reconstructionBox rx ry) ry eta →
      FirstOrderComponentJetsAgreeAt
        (actualFirstOrderState eta)
        (actualFirstOrderState (reconstructedSeriesGamma a)) (0, 0) := by
    intro eta heta
    exact
      _root_.StressTensor.CKAnalyticCompetitorPDE.IsCKSolution.actualFirstOrderState_componentJetsAgree
        P heta hrx hry hreconstructed
  exact ⟨
    { rx := rx
      ry := ry
      rx_pos := hrx
      ry_pos := hry
      outcome :=
        ckOutcome_reconstructionBox_of_series_of_componentJet_determinacy_of_noncharacteristic
          hgeom hrx hry hxrate hyrate hrow hid hnonchar hdet }⟩

/-- A chosen complete outcome package.  The choice is local to Lean's
noncomputable logic; existence is proved by
`nonempty_positiveCKOutcomeData`. -/
noncomputable def positiveCKOutcomeData (P : Params) :
    PositiveCKOutcomeData P :=
  Classical.choice (nonempty_positiveCKOutcomeData P)

/-- Existential packaging of the complete local CK construction.  A sigma
type is used because `CKOutcome` is data in `Type`, not a proposition. -/
theorem nonempty_ckOutcome_reconstructionBox (P : Params) :
    Nonempty (Σ rx : ℝ, Σ ry : ℝ,
      CKOutcome P (reconstructionBox rx ry) ry) := by
  let D := positiveCKOutcomeData P
  exact ⟨⟨D.rx, D.ry, D.outcome⟩⟩

end

end CKCompleteOutcome
end StressTensor
