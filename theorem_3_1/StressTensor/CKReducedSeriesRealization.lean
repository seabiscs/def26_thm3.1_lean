import StressTensor.CKVectorAnalyticEvaluation
import StressTensor.CKFirstOrderAnalyticData
import StressTensor.CKSeriesPrimitive
import StressTensor.FirstOrderReconstruction

/-!
# From convergent reduced coefficients to an actual first-order solution

This file is the verification half of the reduced Cauchy--Kowalevskaya
construction.  It does not assume that a formal coefficient array represents
its derivatives: a common geometric bound supplies convergence and the
termwise-derivative theorems.  Consequently, the two identities between the
evaluated coefficient series imply the genuine pointwise differential
equations for the analytic vector-valued sum.
-/

namespace StressTensor
namespace CKReducedSeriesRealization

open CKPowerSeries CKGeometricMajorant CKVectorAnalyticEvaluation CKSeriesPrimitive

noncomputable section

/-- An actual two-component reduced field, curried in `(x,y)`. -/
abbrev ReducedField := ℝ → ℝ → FirstOrderState

/-- The reduced coefficient phase `(y,v,r)` associated with an actual state. -/
def reducedFieldPhase (U : ReducedField) (x y : ℝ) : FirstOrderPhase :=
  firstOrderPhase y (U x y 0) (U x y 1)

/-- The closed two-component first-order system, stated directly for an
independent state `(v,r)`. -/
def ReducedSystemAt (P : Params) (U : ReducedField) (x y : ℝ) : Prop :=
  deriv (fun xi => U xi y 0) x =
      firstOrderVRate P (reducedFieldPhase U x y)
        (deriv (fun eta => U x eta 0) y)
        (deriv (fun eta => U x eta 1) y) ∧
    deriv (fun xi => U xi y 1) x =
      firstOrderRRate (reducedFieldPhase U x y)
        (deriv (fun eta => U x eta 0) y)

/-- The vector-valued presentation is definitionally the independently
curried system used by the reconstruction theorem. -/
theorem reducedSystemAt_iff_components
    (P : Params) (U : ReducedField) (x y : ℝ) :
    ReducedSystemAt P U x y ↔
      ReducedFirstOrderSystemAt P
        (fun xi eta => U xi eta 0) (fun xi eta => U xi eta 1) x y := by
  rfl

/-- The phase assembled directly from a pair of coefficient arrays. -/
def reducedSeriesPhase (a : VectorCoeff (Fin 2)) (x y : ℝ) : FirstOrderPhase :=
  firstOrderPhase y (eval (a 0) x y) (eval (a 1) x y)

/-- The two formal identities after all convergent series have been
evaluated.  `CKReducedSeriesRealization` turns these into actual derivative
identities; the outstanding coefficient construction must establish them
from the coefficient recurrence. -/
def ReducedSeriesIdentityAt
    (P : Params) (a : VectorCoeff (Fin 2)) (x y : ℝ) : Prop :=
  xDerivativeEval (a 0) x y =
      firstOrderVRate P (reducedSeriesPhase a x y)
        (yDerivativeEval (a 0) x y)
        (yDerivativeEval (a 1) x y) ∧
    xDerivativeEval (a 1) x y =
      firstOrderRRate (reducedSeriesPhase a x y)
        (yDerivativeEval (a 0) x y)

/-- The vector-valued series viewed as a curried reduced field. -/
def reducedSeriesField (a : VectorCoeff (Fin 2)) : ReducedField :=
  fun x y => vectorEval a (x, y)

@[simp] theorem reducedSeriesField_apply
    (a : VectorCoeff (Fin 2)) (x y : ℝ) (i : Fin 2) :
    reducedSeriesField a x y i = eval (a i) x y := rfl

@[simp] theorem reducedFieldPhase_reducedSeriesField
    (a : VectorCoeff (Fin 2)) (x y : ℝ) :
    reducedFieldPhase (reducedSeriesField a) x y =
      reducedSeriesPhase a x y := rfl

/-- On a strict convergence box, the evaluated formal identities are the
actual reduced PDE. -/
theorem reducedSystemAt_of_reducedSeriesIdentityAt
    {P : Params} {a : VectorCoeff (Fin 2)} {M sx sy rx ry x y : ℝ}
    (hgeom : VectorGeometricBound a M sx sy)
    (hrx : 0 < rx) (hry : 0 < ry)
    (hxrate : (sx + 1) * rx < 1) (hyrate : (sy + 1) * ry < 1)
    (hx : |x| < rx) (hy : |y| < ry)
    (hid : ReducedSeriesIdentityAt P a x y) :
    ReducedSystemAt P (reducedSeriesField a) x y := by
  unfold ReducedSystemAt
  simp only [reducedSeriesField]
  rw [hgeom.deriv_vectorEval_x hrx hry hxrate hyrate hx hy.le 0,
    hgeom.deriv_vectorEval_y hrx hry hxrate hyrate hx.le hy 0,
    hgeom.deriv_vectorEval_y hrx hry hxrate hyrate hx.le hy 1,
    hgeom.deriv_vectorEval_x hrx hry hxrate hyrate hx hy.le 1]
  simpa only [ReducedSeriesIdentityAt,
    reducedFieldPhase_reducedSeriesField] using hid

/-- Uniform evaluated series identities give the genuine system everywhere
on the centered open box. -/
theorem reducedSystemOn_of_reducedSeriesIdentityOn
    {P : Params} {a : VectorCoeff (Fin 2)} {M sx sy rx ry : ℝ}
    (hgeom : VectorGeometricBound a M sx sy)
    (hrx : 0 < rx) (hry : 0 < ry)
    (hxrate : (sx + 1) * rx < 1) (hyrate : (sy + 1) * ry < 1)
    (hid : ∀ x y, |x| < rx → |y| < ry →
      ReducedSeriesIdentityAt P a x y) :
    ∀ x y, |x| < rx → |y| < ry →
      ReducedSystemAt P (reducedSeriesField a) x y := by
  intro x y hx hy
  exact reducedSystemAt_of_reducedSeriesIdentityAt hgeom hrx hry
    hxrate hyrate hx hy (hid x y hx hy)

/-- Direct form consumable by `FirstOrderReconstruction`: the two scalar
component sums satisfy its independently-curried reduced system. -/
theorem reducedFirstOrderSystemAt_of_reducedSeriesIdentityAt
    {P : Params} {a : VectorCoeff (Fin 2)} {M sx sy rx ry x y : ℝ}
    (hgeom : VectorGeometricBound a M sx sy)
    (hrx : 0 < rx) (hry : 0 < ry)
    (hxrate : (sx + 1) * rx < 1) (hyrate : (sy + 1) * ry < 1)
    (hx : |x| < rx) (hy : |y| < ry)
    (hid : ReducedSeriesIdentityAt P a x y) :
    ReducedFirstOrderSystemAt P
      (fun xi eta => reducedSeriesField a xi eta 0)
      (fun xi eta => reducedSeriesField a xi eta 1) x y := by
  exact (reducedSystemAt_iff_components P (reducedSeriesField a) x y).1
    (reducedSystemAt_of_reducedSeriesIdentityAt hgeom hrx hry
      hxrate hyrate hx hy hid)

/-- The realized reduced field is genuinely analytic on the convergence
box. -/
theorem analyticOnNhd_uncurried_reducedSeriesField
    {a : VectorCoeff (Fin 2)} {M sx sy rx ry : ℝ}
    (hgeom : VectorGeometricBound a M sx sy)
    (hrx : 0 < rx) (hry : 0 < ry)
    (hxrate : (sx + 1) * rx < 1) (hyrate : (sy + 1) * ry < 1) :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ => reducedSeriesField a p.1 p.2)
      (Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry) := by
  simpa only [reducedSeriesField] using
    hgeom.analyticOnNhd_vectorEval hrx hry hxrate hyrate

/-- A zero zeroth `x` row evaluates to zero on the Cauchy axis. -/
theorem eval_zero_x_of_zero_row {a : Coeff}
    (hrow : ∀ n, a 0 n = 0) (y : ℝ) :
    eval a 0 y = 0 := by
  unfold eval
  calc
    (∑' m, rowEval a m y * 0 ^ m) = ∑' _m : ℕ, 0 := by
      apply tsum_congr
      intro m
      cases m with
      | zero => simp [rowEval, rowTerm, hrow]
      | succ m => simp
    _ = 0 := tsum_zero

/-- Zero zeroth rows give the zero vector Cauchy datum exactly, without a
separate convergence assumption. -/
theorem reducedSeriesField_zero_x_of_zero_rows
    {a : VectorCoeff (Fin 2)}
    (hrow : ∀ i n, a i 0 n = 0) (y : ℝ) :
    reducedSeriesField a 0 y = 0 := by
  funext i
  simpa using eval_zero_x_of_zero_row (hrow i) y

/-- A convergent analytic reduced series with zero zeroth rows and the
evaluated second reduced identity supplies the complete *local*
reconstruction package.  In particular, continuity of the `x`-slices and
differentiation under the reconstruction integral are no longer separate
hypotheses: they follow from the componentwise analyticity proved above. -/
theorem analyticFirstOrderReconstructionData_of_reducedSeriesIdentityOn
    {P : Params} {a : VectorCoeff (Fin 2)} {M sx sy rx ry : ℝ}
    (hgeom : VectorGeometricBound a M sx sy)
    (hrx : 0 < rx) (hry : 0 < ry)
    (hxrate : (sx + 1) * rx < 1) (hyrate : (sy + 1) * ry < 1)
    (hrow : ∀ i n, a i 0 n = 0)
    (hid : ∀ x y, |x| < rx → |y| < ry →
      ReducedSeriesIdentityAt P a x y) :
    AnalyticFirstOrderReconstructionData
      (fun x y => reducedSeriesField a x y 0)
      (fun x y => reducedSeriesField a x y 1) rx ry := by
  have hvec := analyticOnNhd_uncurried_reducedSeriesField
    hgeom hrx hry hxrate hyrate
  have hcomponent := analyticOnNhd_pi_iff.mp hvec
  refine
    { rx_pos := hrx
      ry_pos := hry
      v_analytic := ?_
      r_analytic := ?_
      v_zero := ?_
      r_zero := ?_
      r_equation := ?_ }
  · change AnalyticOnNhd ℝ (fun p : Point => eval (a 0) p.1 p.2)
      (Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry)
    exact hcomponent 0
  · change AnalyticOnNhd ℝ (fun p : Point => eval (a 1) p.1 p.2)
      (Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry)
    exact hcomponent 1
  · intro y _hy
    exact eval_zero_x_of_zero_row (hrow 0) y
  · intro y _hy
    exact eval_zero_x_of_zero_row (hrow 1) y
  · intro x y hx hy
    have hsys := reducedSystemAt_of_reducedSeriesIdentityAt
      hgeom hrx hry hxrate hyrate hx hy (hid x y hx hy)
    simpa [ReducedSystemAt, reducedFieldPhase, partialY] using hsys.2

/-! ## The analytic primitive is the integral reconstruction -/

/-- On the common convergence box, the integral reconstruction of one
scalar series is exactly the evaluated zero-initial-value coefficient
primitive.  This bridges the measure-theoretic reconstruction to the
analytic power-series realization. -/
theorem reconstructedH_eval_eq_eval_xPrimitiveCoeff
    {a : Coeff} {M sx sy rx ry x y : ℝ}
    (hgeom : GeometricBound a M sx sy)
    (hrx : 0 < rx) (hry : 0 < ry)
    (hxrate : (sx + 1) * rx < 1) (hyrate : (sy + 1) * ry < 1)
    (hx : |x| < rx) (hy : |y| < ry) :
    reconstructedH (fun xi eta => eval a xi eta) x y =
      eval (xPrimitiveCoeff a) x y := by
  have hxmono : max 1 sx ≤ sx + 1 := by
    apply max_le
    · linarith [hgeom.sx_nonneg]
    · linarith
  have hxprim : max 1 sx * rx < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hxmono hrx.le) hxrate
  have hyprim : sy * ry < 1 := by
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (by linarith : sy ≤ sy + 1) hry.le)
      hyrate
  have hvAnalyticDirect := hgeom.analyticOnNhd_eval hrx hry hxrate hyrate
  have hvAnalytic : AnalyticOnNhd ℝ
      (uncurried (fun xi eta => eval a xi eta))
      (reconstructionBox rx ry) := by
    change AnalyticOnNhd ℝ (fun p : Point => eval a p.1 p.2)
      (Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry)
    exact hvAnalyticDirect
  have hprimAnalytic := analyticOnNhd_eval_xPrimitiveCoeff_same_box
    hgeom hrx hry hxrate hyrate
  let F : ℝ → ℝ := fun s =>
    eval (xPrimitiveCoeff a) s y -
      reconstructedH (fun xi eta => eval a xi eta) s y
  have hF : ∀ s ∈ Set.uIcc (0 : ℝ) x, HasDerivAt F 0 s := by
    intro s hs
    have hsx := abs_lt_of_mem_uIcc_zero hx hs
    have hpAt := hprimAnalytic (s, y)
      ⟨abs_lt.mp hsx, abs_lt.mp hy⟩
    have hpSlice : AnalyticAt ℝ
        (fun z => eval (xPrimitiveCoeff a) z y) s := hpAt.curry_left
    have hpDeriv : HasDerivAt
        (fun z => eval (xPrimitiveCoeff a) z y) (eval a s y) s :=
      hpSlice.differentiableAt.hasDerivAt.congr_deriv
        (deriv_eval_xPrimitiveCoeff hgeom hrx hry hxprim hyprim hsx hy.le)
    have hhDeriv := hasDerivAt_reconstructedH_x_of_analyticOnNhd
      hvAnalytic hsx hy
    have hraw := hpDeriv.sub hhDeriv
    have hzero : HasDerivAt
        (fun z => eval (xPrimitiveCoeff a) z y -
          reconstructedH (fun xi eta => eval a xi eta) z y) 0 s :=
      hraw.congr_deriv (by simp)
    apply hzero.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun _ => rfl
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (continuous_const.intervalIntegrable (0 : ℝ) x)
  have hF0 : F 0 = 0 := by
    simp [F]
  have hFx : F x = 0 := by
    have h := hFTC
    simp [hF0] at h
    linarith
  dsimp only [F] at hFx
  linarith

/-- Consequently, the integral reconstruction of the first reduced series
is analytic on exactly the same centered convergence box.  This removes the
last separate `AnalyticAt gamma` assumption from the series-level
reconstruction pipeline. -/
theorem analyticOnNhd_uncurried_reconstructedGamma_reducedSeries
    {a : VectorCoeff (Fin 2)} {M sx sy rx ry : ℝ}
    (hgeom : VectorGeometricBound a M sx sy)
    (hrx : 0 < rx) (hry : 0 < ry)
    (hxrate : (sx + 1) * rx < 1) (hyrate : (sy + 1) * ry < 1) :
    AnalyticOnNhd ℝ
      (uncurried (reconstructedGamma
        (fun x y => reducedSeriesField a x y 0)))
      (reconstructionBox rx ry) := by
  let v : ℝ → ℝ → ℝ := fun x y => reducedSeriesField a x y 0
  have hprim := analyticOnNhd_eval_xPrimitiveCoeff_same_box
    (hgeom.component 0) hrx hry hxrate hyrate
  have hseries : AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ => eval (xPrimitiveCoeff (a 0)) p.1 p.2 - p.1)
      (Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry) :=
    hprim.sub analyticOnNhd_fst
  change AnalyticOnNhd ℝ
    (fun p : Point => reconstructedGamma v p.1 p.2)
    (Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry)
  apply hseries.congr (isOpen_Ioo.prod isOpen_Ioo)
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  change eval (xPrimitiveCoeff (a 0)) x y - x =
    reconstructedGamma v x y
  rw [reconstructedGamma]
  change eval (xPrimitiveCoeff (a 0)) x y - x =
    reconstructedH (fun xi eta => eval (a 0) xi eta) x y - x
  rw [
    reconstructedH_eval_eq_eval_xPrimitiveCoeff
      (hgeom.component 0) hrx hry hxrate hyrate
      (abs_lt.mpr hx) (abs_lt.mpr hy)]

/-- End-to-end reconstruction theorem for an evaluated reduced coefficient
solution.  Geometric convergence, zero rows, and the two evaluated formal
identities imply the original auxiliary equation at every point where its
leading coefficient is nonzero, together with the full Cauchy data.  All
regularity and differentiation-under-the-integral obligations are discharged
internally. -/
theorem reconstructedGamma_auxiliaryEquationAt_and_cauchyData_of_series
    {P : Params} {a : VectorCoeff (Fin 2)} {M sx sy rx ry x y : ℝ}
    (hgeom : VectorGeometricBound a M sx sy)
    (hrx : 0 < rx) (hry : 0 < ry)
    (hxrate : (sx + 1) * rx < 1) (hyrate : (sy + 1) * ry < 1)
    (hrow : ∀ i n, a i 0 n = 0)
    (hid : ∀ x y, |x| < rx → |y| < ry →
      ReducedSeriesIdentityAt P a x y)
    (hx : |x| < rx) (hy : |y| < ry)
    (hcoeff0 : firstOrderCoeff0 P (reducedSeriesPhase a x y) ≠ 0) :
    auxiliaryEquationAt P
        (reconstructedGamma
          (fun xi eta => reducedSeriesField a xi eta 0)) x y ∧
      HasCauchyDataOn
        (reconstructedGamma
          (fun xi eta => reducedSeriesField a xi eta 0)) ry := by
  let v : ℝ → ℝ → ℝ := fun xi eta => reducedSeriesField a xi eta 0
  let r : ℝ → ℝ → ℝ := fun xi eta => reducedSeriesField a xi eta 1
  have D : AnalyticFirstOrderReconstructionData v r rx ry := by
    simpa only [v, r] using
      analyticFirstOrderReconstructionData_of_reducedSeriesIdentityOn
        hgeom hrx hry hxrate hyrate hrow hid
  have hgamma : AnalyticAt ℝ (uncurried (reconstructedGamma v)) (x, y) := by
    simpa only [v] using
      (analyticOnNhd_uncurried_reconstructedGamma_reducedSeries
        hgeom hrx hry hxrate hyrate) (x, y)
          (mem_reconstructionBox.2 ⟨hx, hy⟩)
  have hsys : ReducedFirstOrderSystemAt P v r x y := by
    simpa only [v, r] using
      reducedFirstOrderSystemAt_of_reducedSeriesIdentityAt
        hgeom hrx hry hxrate hyrate hx hy (hid x y hx hy)
  have hcoeff0' : firstOrderCoeff0 P
      (firstOrderPhase y (v x y) (r x y)) ≠ 0 := by
    change firstOrderCoeff0 P
      (firstOrderPhase y (eval (a 0) x y) (eval (a 1) x y)) ≠ 0
    exact hcoeff0
  exact ⟨D.auxiliaryEquationAt_gamma_of_analyticAt P hx hy
      hgamma hcoeff0' hsys,
    D.reconstructedGamma_hasCauchyDataOn⟩

end

end CKReducedSeriesRealization
end StressTensor
