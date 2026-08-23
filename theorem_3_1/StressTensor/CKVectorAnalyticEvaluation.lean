import StressTensor.CKAnalyticEvaluation

/-!
# Analytic realization of finite-dimensional coefficient arrays

The reduced stress-tensor equation has two unknown components.  The scalar
realization theorem in `CKAnalyticEvaluation` applies componentwise; this file
packages the resulting statement for a finite `Pi`-valued field and records
that no extra convergence assumption is hidden in passing from scalar series
to the vector state.
-/

namespace StressTensor
namespace CKVectorAnalyticEvaluation

open CKPowerSeries CKGeometricMajorant

noncomputable section

variable {ι : Type*}

/-- A finite family of bivariate scalar coefficient arrays. -/
abbrev VectorCoeff (ι : Type*) := ι → Coeff

/-- Bivariate coefficients with values in a finite real coordinate space. -/
abbrev StateCoeff (ι : Type*) := ℕ → ℕ → (ι → ℝ)

/-- Extract the scalar coefficient array of one state component. -/
def componentCoeff (u : StateCoeff ι) (i : ι) : Coeff :=
  fun m n => u m n i

/-- Repackage state-valued coefficients as their family of scalar component
arrays. -/
def stateComponents (u : StateCoeff ι) : VectorCoeff ι :=
  fun i => componentCoeff u i

/-- Componentwise evaluation of a finite family of bivariate series. -/
def vectorEval (a : VectorCoeff ι) (p : ℝ × ℝ) : ι → ℝ :=
  fun i => eval (a i) p.1 p.2

/-- A single set of geometric constants controlling every component. -/
structure VectorGeometricBound (a : VectorCoeff ι)
    (M sx sy : ℝ) : Prop where
  component : ∀ i, GeometricBound (a i) M sx sy

/-- A geometric estimate in the finite-product norm automatically controls
all scalar component arrays with the same constants. -/
theorem vectorGeometricBound_of_state_norm_bound
    [Fintype ι] {u : StateCoeff ι} {M sx sy : ℝ}
    (hM : 0 ≤ M) (hsx : 0 ≤ sx) (hsy : 0 ≤ sy)
    (hu : ∀ m n, ‖u m n‖ ≤ M * sx ^ m * sy ^ n) :
    VectorGeometricBound (stateComponents u) M sx sy := by
  refine ⟨fun i => ⟨hM, hsx, hsy, ?_⟩⟩
  intro m n
  rw [stateComponents, componentCoeff, ← Real.norm_eq_abs]
  exact (norm_le_pi_norm (u m n) i).trans (hu m n)

namespace VectorGeometricBound

variable {a : VectorCoeff ι} {M sx sy : ℝ}

theorem M_nonneg [Nonempty ι]
    (h : VectorGeometricBound a M sx sy) : 0 ≤ M :=
  (h.component (Classical.arbitrary ι)).M_nonneg

theorem sx_nonneg [Nonempty ι]
    (h : VectorGeometricBound a M sx sy) : 0 ≤ sx :=
  (h.component (Classical.arbitrary ι)).sx_nonneg

theorem sy_nonneg [Nonempty ι]
    (h : VectorGeometricBound a M sx sy) : 0 ≤ sy :=
  (h.component (Classical.arbitrary ι)).sy_nonneg

/-- A common product-geometric bound realizes the finite vector series as a
real-analytic field on every strictly smaller centered box. -/
theorem analyticOnNhd_vectorEval
    [Fintype ι]
    (h : VectorGeometricBound a M sx sy)
    {rx ry : ℝ} (hrx : 0 < rx) (hry : 0 < ry)
    (hx : (sx + 1) * rx < 1) (hy : (sy + 1) * ry < 1) :
    AnalyticOnNhd ℝ (vectorEval a)
      (Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry) := by
  apply AnalyticOnNhd.pi
  intro i
  simpa only [vectorEval] using
    (h.component i).analyticOnNhd_eval hrx hry hx hy

/-- The same conclusion with already-positive rates, without the harmless
rate enlargement used to cover zero rates. -/
theorem analyticOnNhd_vectorEval_of_pos_rates
    [Fintype ι]
    (h : VectorGeometricBound a M sx sy)
    (hsx : 0 < sx) (hsy : 0 < sy)
    {rx ry : ℝ} (hrx : 0 < rx) (hry : 0 < ry)
    (hx : sx * rx < 1) (hy : sy * ry < 1) :
    AnalyticOnNhd ℝ (vectorEval a)
      (Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry) := by
  apply AnalyticOnNhd.pi
  intro i
  simpa only [vectorEval] using
    (h.component i).analyticOnNhd_eval_of_pos_rates
      hsx hsy hrx hry hx hy

/-- Componentwise differentiation in the evolution variable agrees with the
termwise differentiated coefficient series. -/
theorem deriv_vectorEval_x
    (h : VectorGeometricBound a M sx sy)
    {rx ry x y : ℝ} (hrx : 0 < rx) (hry : 0 < ry)
    (hxrate : (sx + 1) * rx < 1) (hyrate : (sy + 1) * ry < 1)
    (hx : |x| < rx) (hy : |y| ≤ ry) (i : ι) :
    deriv (fun z => vectorEval a (z, y) i) x =
      xDerivativeEval (a i) x y := by
  let hi := (h.component i).enlargeRates
  exact CKPowerSeries.deriv_eval_x
    (hi.summableOnBox hrx.le hry.le hxrate hyrate)
    (hi.summableXDerivativeOnBox hrx hry.le hxrate hyrate)
    hrx hx hy

/-- Componentwise differentiation in the tangential variable agrees with
the termwise differentiated coefficient series. -/
theorem deriv_vectorEval_y
    (h : VectorGeometricBound a M sx sy)
    {rx ry x y : ℝ} (hrx : 0 < rx) (hry : 0 < ry)
    (hxrate : (sx + 1) * rx < 1) (hyrate : (sy + 1) * ry < 1)
    (hx : |x| ≤ rx) (hy : |y| < ry) (i : ι) :
    deriv (fun z => vectorEval a (x, z) i) y =
      yDerivativeEval (a i) x y := by
  let hi := (h.component i).enlargeRates
  exact CKPowerSeries.deriv_eval_y
    (hi.summableOnBox hrx.le hry.le hxrate hyrate)
    (hi.summableYDerivativeOnBox hrx.le hry hxrate hyrate)
    hry hx hy

end VectorGeometricBound

end

end CKVectorAnalyticEvaluation
end StressTensor
