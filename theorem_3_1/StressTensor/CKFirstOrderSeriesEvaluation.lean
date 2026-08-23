import StressTensor.CKAnalyticCompetitorRecurrence
import StressTensor.CKFormalRecurrenceDiagonalIdentity
import StressTensor.CKFirstOrderVectorRHS
import StressTensor.CKReducedSeriesRealization
import StressTensor.CKPolarEvaluation

/-!
# Analytic evaluation of the formal first-order solution

A common geometric bound on the two component arrays turns the formal
coefficient solution into an actual analytic vector field.  The exact formal
recurrence then identifies its `x` derivative with the analytic reduced
right-hand side as germs at the origin.  Finally, the Fréchet-derivative and
termwise-evaluation bridges convert that germ identity into the scalar
`ReducedSeriesIdentityAt` used by the reconstruction layer.
-/

namespace StressTensor
namespace CKFirstOrderSeriesEvaluation

open CKPowerSeries CKVectorAnalyticEvaluation CKFirstOrderFormalSystem
  CKAnalyticCompetitorRecurrence CKFormalRecurrenceDiagonalIdentity
  CKReducedSeriesRealization

noncomputable section

/-! ## A uniform interior radius -/

private def safeRadius (s : ℝ) : ℝ := (2 * (s + 1))⁻¹

private theorem safeRadius_pos {s : ℝ} (hs : 0 ≤ s) :
    0 < safeRadius s := by
  unfold safeRadius
  positivity

private theorem enlargedRate_mul_safeRadius_lt_one
    {s : ℝ} (hs : 0 ≤ s) :
    (s + 1) * safeRadius s < 1 := by
  unfold safeRadius
  have hs1 : s + 1 ≠ 0 := by linarith
  field_simp
  linarith

/-! ## The evaluated state and its power series -/

/-- Scalar component arrays of the selected formal first-order solution. -/
abbrev firstOrderSeriesComponents (P : Params) : VectorCoeff (Fin 2) :=
  stateComponents (firstOrderFormalCoefficients P)

/-- The actual vector field obtained by evaluating both formal component
series. -/
def firstOrderSeriesState (P : Params) : Domain → FirstOrderState :=
  vectorEval (firstOrderSeriesComponents P)

/-- A common componentwise geometric bound realizes the evaluated field
with exactly the canonical bivariate state FMS selected by the recurrence. -/
theorem hasFPowerSeriesAt_firstOrderSeriesState
    (P : Params) {M sx sy : ℝ}
    (hgeom : VectorGeometricBound (firstOrderSeriesComponents P) M sx sy) :
    HasFPowerSeriesAt (firstOrderSeriesState P)
      (stateBivariateFMS (firstOrderFormalCoefficients P)) 0 := by
  have hsx : 0 ≤ sx := hgeom.sx_nonneg
  have hsy : 0 ≤ sy := hgeom.sy_nonneg
  let rx := safeRadius sx
  let ry := safeRadius sy
  have hrx : 0 < rx := safeRadius_pos hsx
  have hry : 0 < ry := safeRadius_pos hsy
  have hxrate' : (sx + 1) * rx < 1 :=
    enlargedRate_mul_safeRadius_lt_one hsx
  have hyrate' : (sy + 1) * ry < 1 :=
    enlargedRate_mul_safeRadius_lt_one hsy
  have hxrate : sx * rx < 1 :=
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (by linarith : sx ≤ sx + 1) hrx.le)
      hxrate'
  have hyrate : sy * ry < 1 :=
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (by linarith : sy ≤ sy + 1) hry.le)
      hyrate'
  have hgeom' := hgeom
  change VectorGeometricBound
    (fun i m n => firstOrderFormalCoefficients P m n i) M sx sy at hgeom'
  have h := CKPolarEvaluation.hasFPowerSeriesAt_stateFMS
    (a := firstOrderFormalCoefficients P) hgeom' hrx hry hxrate hyrate
  change HasFPowerSeriesAt
    (fun p : ℝ × ℝ => fun i : Fin 2 =>
      eval (fun m n => firstOrderFormalCoefficients P m n i) p.1 p.2)
    (stateBivariateFMS (firstOrderFormalCoefficients P)) 0
  simpa [stateBivariateFMS, CKPolarEvaluation.stateFMS] using h

/-! ## Analyticity of the reduced right-hand side -/

/-- The analytic phase, Euler field, principal matrix, and source combine
to give an actual FMS representative of the pointwise reduced RHS. -/
theorem exists_hasFPowerSeriesAt_actualReducedRHS
    {Nfun : FirstOrderPhase → FirstOrderOperator}
    {bfun : FirstOrderPhase → FirstOrderState}
    {U : Domain → FirstOrderState}
    {N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator}
    {b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState}
    {u : StateSeries}
    (hN : HasFPowerSeriesAt Nfun N 0)
    (hb : HasFPowerSeriesAt bfun b 0)
    (hu : HasFPowerSeriesAt U u 0)
    (hU0 : U 0 = 0) :
    ∃ r : StateSeries,
      HasFPowerSeriesAt (actualReducedRHS Nfun bfun U) r 0 := by
  have hphase := hasFPowerSeriesAt_phaseSeries hu
  have hphase0 : actualPhase U 0 = 0 := by
    simp [actualPhase, hU0, firstOrderPhase]
  have hN0 : HasFPowerSeriesAt Nfun N (actualPhase U 0) := by
    simpa only [hphase0] using hN
  have hb0 : HasFPowerSeriesAt bfun b (actualPhase U 0) := by
    simpa only [hphase0] using hb
  have hNcomp : HasFPowerSeriesAt (Nfun ∘ actualPhase U)
      (N.comp (phaseSeries u)) 0 := hN0.comp hphase
  have hbcomp : HasFPowerSeriesAt (bfun ∘ actualPhase U)
      (b.comp (phaseSeries u)) 0 := hb0.comp hphase
  obtain ⟨e, he⟩ := exists_hasFPowerSeriesAt_actualEuler hu
  have hpair := hNcomp.prod he
  let Φ : Domain → FirstOrderOperator × FirstOrderState :=
    fun z => (Nfun (actualPhase U z),
      z.2 • fderiv ℝ U z yDirection)
  have hB := operatorActionCLM.hasFPowerSeriesAt_bilinear (Φ 0)
  have haction := hB.comp hpair
  have hsum := haction.add hbcomp
  have hsum' : HasFPowerSeriesAt (actualReducedRHS Nfun bfun U)
      ((operatorActionCLM.fpowerSeriesBilinear (Φ 0)).comp
          ((N.comp (phaseSeries u)).prod e) + b.comp (phaseSeries u)) 0 := by
    convert hsum using 1
    funext z
    rfl
  exact ⟨_, hsum'⟩

/-- The evaluated formal state takes the prescribed zero value at the
origin. -/
theorem firstOrderSeriesState_zero
    (P : Params) {M sx sy : ℝ}
    (hgeom : VectorGeometricBound (firstOrderSeriesComponents P) M sx sy) :
    firstOrderSeriesState P 0 = 0 := by
  have hu := hasFPowerSeriesAt_firstOrderSeriesState P hgeom
  have hcoeff := hu.coeff_zero (fun _ : Fin 0 => (0 : Domain))
  have hzero :
      stateBivariateFMS (firstOrderFormalCoefficients P) 0
          (fun _ : Fin 0 => (0 : Domain)) = 0 := by
    rw [CKPolarUniqueness.stateBivariateFMS_apply_diag]
    simp [firstOrderFormalCoefficients_zero_x]
  exact hcoeff.symm.trans hzero

/-! ## The analytic reduced equation -/

/-- The derivative of the evaluated formal state and the actual reduced
right-hand side agree on a neighborhood of the origin.

The proof compares their analytic FMS representatives.  The public raw-`x`
derivative bridge converts the derivative FMS to the canonical derivative
array, and the formal recurrence diagonal identity converts that array to
the formal reduced RHS. -/
theorem eventuallyEq_fderiv_firstOrderSeriesState_xDirection_actualReducedRHS
    (P : Params) {M sx sy : ℝ}
    (hgeom : VectorGeometricBound (firstOrderSeriesComponents P) M sx sy) :
    (fun z => fderiv ℝ (firstOrderSeriesState P) z xDirection) =ᶠ[nhds 0]
      actualReducedRHS (firstOrderPrincipalArray P)
        (firstOrderSourceVector P) (firstOrderSeriesState P) := by
  let a := firstOrderFormalCoefficients P
  let u := stateBivariateFMS a
  let U := firstOrderSeriesState P
  let N := (firstOrderPrincipalOriginMajorant P).series
  let b := (firstOrderSourceOriginMajorant P).series
  have hu : HasFPowerSeriesAt U u 0 := by
    simpa only [U, u, a] using
      hasFPowerSeriesAt_firstOrderSeriesState P hgeom
  have hU0 : U 0 = 0 := by
    simpa only [U] using firstOrderSeriesState_zero P hgeom
  have hN : HasFPowerSeriesAt (firstOrderPrincipalArray P) N 0 := by
    simpa only [N, firstOrderOrigin] using
      (firstOrderPrincipalOriginMajorant P).hasFPowerSeriesOnBall.hasFPowerSeriesAt
  have hb : HasFPowerSeriesAt (firstOrderSourceVector P) b 0 := by
    simpa only [b, firstOrderOrigin] using
      (firstOrderSourceOriginMajorant P).hasFPowerSeriesOnBall.hasFPowerSeriesAt
  obtain ⟨r, hr⟩ := exists_hasFPowerSeriesAt_actualReducedRHS
    hN hb hu hU0
  have hx := hasFPowerSeriesAt_rawFormalXDerivative hu
  apply CKPolarUniqueness.eventuallyEq_of_hasFPowerSeriesAt_of_apply_diag_eq
    hx hr
  intro k z
  calc
    rawFormalXDerivative u k (fun _ : Fin k => z) =
        stateBivariateFMS (xDerivativeCoefficientArray a) k
          (fun _ : Fin k => z) := by
      exact rawFormalXDerivative_stateBivariateFMS_apply_diag
        a k z.1 z.2
    _ = reducedRHS N b u k (fun _ : Fin k => z) := by
      exact stateBivariateFMS_xDerivativeCoefficientArray_apply_diag
        N b a (firstOrderFormalCoefficients_satisfiesRecurrence P)
          k z.1 z.2
    _ = r k (fun _ : Fin k => z) := by
      exact (reducedRHS_diagonal_eq_of_hasFPowerSeriesAt
        hN hb hu hU0 hr k z).symm

/-! ## Scalar evaluated series identity -/

/-- On some neighborhood of the origin, the two evaluated scalar component
series satisfy the exact identities consumed by the reconstruction layer. -/
theorem eventually_reducedSeriesIdentityAt_firstOrderFormalCoefficients
    (P : Params) {M sx sy : ℝ}
    (hgeom : VectorGeometricBound (firstOrderSeriesComponents P) M sx sy) :
    ∀ᶠ z : Domain in nhds 0,
      ReducedSeriesIdentityAt P (firstOrderSeriesComponents P) z.1 z.2 := by
  let a := firstOrderSeriesComponents P
  let U := firstOrderSeriesState P
  let rx := safeRadius sx
  let ry := safeRadius sy
  have hsx : 0 ≤ sx := hgeom.sx_nonneg
  have hsy : 0 ≤ sy := hgeom.sy_nonneg
  have hrx : 0 < rx := safeRadius_pos hsx
  have hry : 0 < ry := safeRadius_pos hsy
  have hxrate : (sx + 1) * rx < 1 :=
    enlargedRate_mul_safeRadius_lt_one hsx
  have hyrate : (sy + 1) * ry < 1 :=
    enlargedRate_mul_safeRadius_lt_one hsy
  have hgeom' : VectorGeometricBound a M sx sy := by
    simpa only [a] using hgeom
  have hanalytic : AnalyticOnNhd ℝ U
      (Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry) := by
    simpa only [U, firstOrderSeriesState, a] using
      hgeom'.analyticOnNhd_vectorEval hrx hry hxrate hyrate
  have hpde :
      (fun z => fderiv ℝ U z xDirection) =ᶠ[nhds 0]
        actualReducedRHS (firstOrderPrincipalArray P)
          (firstOrderSourceVector P) U := by
    simpa only [U] using
      eventuallyEq_fderiv_firstOrderSeriesState_xDirection_actualReducedRHS
        P hgeom
  have hopen : IsOpen (Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry) :=
    isOpen_Ioo.prod isOpen_Ioo
  have hzero : (0 : Domain) ∈
      (Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry) := by
    simp [hrx, hry]
  have hbox : ∀ᶠ z : Domain in nhds 0,
      z ∈ (Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry) :=
    hopen.mem_nhds hzero
  filter_upwards [hpde, hbox] with z hzPDE hzbox
  have hdiff : DifferentiableAt ℝ U z :=
    (hanalytic z hzbox).differentiableAt
  have hxdir :
      fderiv ℝ U z xDirection =
        fun i => deriv (fun xi => U (xi, z.2) i) z.1 := by
    simpa only [xDirection] using fderiv_apply_xDirection_eq hdiff
  have hydir :
      fderiv ℝ U z yDirection =
        fun i => deriv (fun eta => U (z.1, eta) i) z.2 := by
    simpa only [yDirection] using fderiv_apply_yDirection_eq hdiff
  have hxabs : |z.1| < rx := abs_lt.mpr hzbox.1
  have hyabs : |z.2| < ry := abs_lt.mpr hzbox.2
  have hx0 := hgeom'.deriv_vectorEval_x hrx hry hxrate hyrate
    hxabs hyabs.le 0
  have hx1 := hgeom'.deriv_vectorEval_x hrx hry hxrate hyrate
    hxabs hyabs.le 1
  have hy0 := hgeom'.deriv_vectorEval_y hrx hry hxrate hyrate
    hxabs.le hyabs 0
  have hy1 := hgeom'.deriv_vectorEval_y hrx hry hxrate hyrate
    hxabs.le hyabs 1
  have hpde' :
      fderiv ℝ U z xDirection =
        ![firstOrderVRate P (actualPhase U z)
            ((fderiv ℝ U z yDirection) 0)
            ((fderiv ℝ U z yDirection) 1),
          firstOrderRRate (actualPhase U z)
            ((fderiv ℝ U z yDirection) 0)] := by
    rw [hzPDE]
    unfold actualReducedRHS
    simpa [actualPhase] using
      firstOrder_vector_rhs_eq P (actualPhase U z)
        (fderiv ℝ U z yDirection)
  rw [hxdir, hydir] at hpde'
  have hpde0 := congrFun hpde' (0 : Fin 2)
  have hpde1 := congrFun hpde' (1 : Fin 2)
  have hphase : actualPhase U z = reducedSeriesPhase a z.1 z.2 := by
    rfl
  unfold ReducedSeriesIdentityAt
  constructor
  · rw [← hx0, ← hy0, ← hy1, ← hphase]
    exact hpde0
  · rw [← hx1, ← hy0, ← hphase]
    exact hpde1

end
end CKFirstOrderSeriesEvaluation
end StressTensor
