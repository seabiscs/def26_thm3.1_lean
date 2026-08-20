import StressTensor.CKReducedSeriesRealization
import StressTensor.CKFirstOrderAnalyticUniqueness

/-!
# Assembly of the manuscript-specific Cauchy--Kowalevskaya outcome

This module is the final interface between the coefficient construction and
the rest of the stress-tensor argument.  Its production theorem assumes only

* one common product-geometric bound for the two reduced coefficient arrays,
* their zero Cauchy rows,
* the two evaluated reduced-system identities throughout a centered box,
* nonvanishing of the reduced leading coefficient there, and
* the equation-specific component-jet determinacy statement for competing
  analytic solutions.

It then constructs an actual `CKOutcome`.  Analyticity of the reconstructed
scalar field, differentiation under its defining integral, the auxiliary
equation, its Cauchy data, and the passage from component-jet determinacy to
scalar local uniqueness are all discharged by prior kernel-checked results.
-/

namespace StressTensor
namespace CKOutcomeAssembly

open CKPowerSeries CKGeometricMajorant CKVectorAnalyticEvaluation
  CKReducedSeriesRealization

noncomputable section

/-- The scalar field reconstructed from the first component of a reduced
coefficient array. -/
def reconstructedSeriesGamma (a : VectorCoeff (Fin 2)) : ℝ → ℝ → ℝ :=
  reconstructedGamma (fun x y => reducedSeriesField a x y 0)

/-- The low-level production assembly theorem.  This version exposes the
precise noncharacteristic hypothesis needed to divide by the leading
coefficient when transferring the reduced system to the auxiliary equation. -/
def ckOutcome_reconstructionBox_of_series_of_componentJet_determinacy_of_noncharacteristic
    {P : Params} {a : VectorCoeff (Fin 2)} {M sx sy rx ry : ℝ}
    (hgeom : VectorGeometricBound a M sx sy)
    (hrx : 0 < rx) (hry : 0 < ry)
    (hxrate : (sx + 1) * rx < 1) (hyrate : (sy + 1) * ry < 1)
    (hrow : ∀ i n, a i 0 n = 0)
    (hid : ∀ x y, |x| < rx → |y| < ry →
      ReducedSeriesIdentityAt P a x y)
    (hnonchar : ∀ x y, |x| < rx → |y| < ry →
      firstOrderCoeff0 P (reducedSeriesPhase a x y) ≠ 0)
    (hdet : ∀ eta : ℝ → ℝ → ℝ,
      IsCKSolution P (reconstructionBox rx ry) ry eta →
      FirstOrderComponentJetsAgreeAt
        (actualFirstOrderState eta)
        (actualFirstOrderState (reconstructedSeriesGamma a)) (0, 0)) :
    CKOutcome P (reconstructionBox rx ry) ry := by
  let gamma : ℝ → ℝ → ℝ := reconstructedSeriesGamma a
  have hanalytic : AnalyticOnNhd ℝ (uncurried gamma)
      (reconstructionBox rx ry) := by
    simpa only [gamma, reconstructedSeriesGamma] using
      analyticOnNhd_uncurried_reconstructedGamma_reducedSeries
        hgeom hrx hry hxrate hyrate
  have hsolves : SolvesAuxiliaryOn P (reconstructionBox rx ry) gamma := by
    intro x y hxy
    rcases mem_reconstructionBox.mp hxy with ⟨hx, hy⟩
    simpa only [gamma, reconstructedSeriesGamma] using
      (reconstructedGamma_auxiliaryEquationAt_and_cauchyData_of_series
        hgeom hrx hry hxrate hyrate hrow hid hx hy
        (hnonchar x y hx hy)).1
  have hx0 : |(0 : ℝ)| < rx := by simpa using hrx
  have hy0 : |(0 : ℝ)| < ry := by simpa using hry
  have hcauchy : HasCauchyDataOn gamma ry := by
    simpa only [gamma, reconstructedSeriesGamma] using
      (reconstructedGamma_auxiliaryEquationAt_and_cauchyData_of_series
        hgeom hrx hry hxrate hyrate hrow hid hx0 hy0
        (hnonchar 0 0 hx0 hy0)).2
  have hsolution : IsCKSolution P (reconstructionBox rx ry) ry gamma :=
    ⟨hanalytic, hsolves, hcauchy⟩
  refine
    { isOpen_domain := ?_
      origin_mem := ?_
      radius_pos := hry
      cauchy_axis_mem := ?_
      gamma := gamma
      solution := hsolution
      locallyUnique := ?_ }
  · unfold reconstructionBox
    exact isOpen_Ioo.prod isOpen_Ioo
  · exact mem_reconstructionBox.mpr ⟨hx0, hy0⟩
  · intro y hy
    exact mem_reconstructionBox.mpr ⟨hx0, hy⟩
  · intro eta heta
    have hgammaCentered :
        IsCKSolution P (centeredAnalyticBox rx ry) ry gamma := by
      simpa only [centeredAnalyticBox, reconstructionBox] using hsolution
    have hetaCentered :
        IsCKSolution P (centeredAnalyticBox rx ry) ry eta := by
      simpa only [centeredAnalyticBox, reconstructionBox] using heta
    have hjets : FirstOrderComponentJetsAgreeAt
        (actualFirstOrderState eta) (actualFirstOrderState gamma) (0, 0) := by
      simpa only [gamma] using hdet eta heta
    have heq := ckSolutions_eqOn_of_actualFirstOrderComponentJets
      hetaCentered hgammaCentered hrx hry le_rfl hjets
    simpa only [centeredAnalyticBox, reconstructionBox] using heq

/-- The coefficient-neighborhood formulation used by the manuscript.  Its
strict positivity theorem supplies the noncharacteristic hypothesis of the
low-level assembly theorem automatically. -/
def ckOutcome_reconstructionBox_of_series_of_componentJet_determinacy
    {P : Params} {a : VectorCoeff (Fin 2)} {M sx sy rx ry : ℝ}
    (hgeom : VectorGeometricBound a M sx sy)
    (hrx : 0 < rx) (hry : 0 < ry)
    (hxrate : (sx + 1) * rx < 1) (hyrate : (sy + 1) * ry < 1)
    (hrow : ∀ i n, a i 0 n = 0)
    (hid : ∀ x y, |x| < rx → |y| < ry →
      ReducedSeriesIdentityAt P a x y)
    (hphase : ∀ x y, |x| < rx → |y| < ry →
      FirstOrderPhaseInU P (reducedSeriesPhase a x y))
    (hdet : ∀ eta : ℝ → ℝ → ℝ,
      IsCKSolution P (reconstructionBox rx ry) ry eta →
      FirstOrderComponentJetsAgreeAt
        (actualFirstOrderState eta)
        (actualFirstOrderState (reconstructedSeriesGamma a)) (0, 0)) :
    CKOutcome P (reconstructionBox rx ry) ry := by
  apply
    ckOutcome_reconstructionBox_of_series_of_componentJet_determinacy_of_noncharacteristic
      hgeom hrx hry hxrate hyrate hrow hid
  · intro x y hx hy
    exact (firstOrderCoeff0_pos_of_inU (hphase x y hx hy)).ne'
  · exact hdet

/-- Coordinate mixed-jet determinacy is an equivalent convenient input for
the production assembly theorem. -/
def ckOutcome_reconstructionBox_of_series_of_coordinateJet_determinacy
    {P : Params} {a : VectorCoeff (Fin 2)} {M sx sy rx ry : ℝ}
    (hgeom : VectorGeometricBound a M sx sy)
    (hrx : 0 < rx) (hry : 0 < ry)
    (hxrate : (sx + 1) * rx < 1) (hyrate : (sy + 1) * ry < 1)
    (hrow : ∀ i n, a i 0 n = 0)
    (hid : ∀ x y, |x| < rx → |y| < ry →
      ReducedSeriesIdentityAt P a x y)
    (hphase : ∀ x y, |x| < rx → |y| < ry →
      FirstOrderPhaseInU P (reducedSeriesPhase a x y))
    (hdet : ∀ eta : ℝ → ℝ → ℝ,
      IsCKSolution P (reconstructionBox rx ry) ry eta →
      FirstOrderCoordinateJetsAgreeAt
        (actualFirstOrderState eta)
        (actualFirstOrderState (reconstructedSeriesGamma a)) (0, 0)) :
    CKOutcome P (reconstructionBox rx ry) ry := by
  apply ckOutcome_reconstructionBox_of_series_of_componentJet_determinacy
    hgeom hrx hry hxrate hyrate hrow hid hphase
  intro eta heta
  exact firstOrderComponentJetsAgreeAt_of_coordinateJets (hdet eta heta)

end

end CKOutcomeAssembly
end StressTensor
