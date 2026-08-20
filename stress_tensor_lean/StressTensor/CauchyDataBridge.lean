import StressTensor.AnalyticInterface
import StressTensor.AxisFormulas

/-!
# From Cauchy data to the initial jet

The prescribed data are constant on the open interval `{y | |y| < r}`.
Consequently their total derivatives vanish there, whether or not separate
differentiability witnesses are supplied.  This identifies the actual jet on
the Cauchy axis with `initialJet`.
-/

namespace StressTensor

noncomputable section

/-- The interval on which the Cauchy data are prescribed is open. -/
theorem isOpen_abs_lt (r : ℝ) : IsOpen {y : ℝ | |y| < r} := by
  exact isOpen_lt continuous_abs continuous_const

/-- The value datum `γ(0,y)=0` makes the transverse derivative vanish in the
interior of the Cauchy interval. -/
theorem partialY_zero_of_cauchyData
    {γ : ℝ → ℝ → ℝ} {r y : ℝ} (hdata : HasCauchyDataOn γ r)
    (hy : |y| < r) : partialY γ 0 y = 0 := by
  let I : Set ℝ := {η | |η| < r}
  have hIopen : IsOpen I := by
    simpa only [I] using isOpen_abs_lt r
  have hval : I.EqOn (γ 0) (fun _η : ℝ => 0) := by
    intro η hη
    exact (hdata hη).1
  simpa only [partialY, deriv_const] using (hval.deriv hIopen hy)

/-- Constancy of `∂ₓγ(0,·)=-1` makes the mixed derivative vanish. -/
theorem partialXY_zero_of_cauchyData
    {γ : ℝ → ℝ → ℝ} {r y : ℝ} (hdata : HasCauchyDataOn γ r)
    (hy : |y| < r) : partialXY γ 0 y = 0 := by
  let I : Set ℝ := {η | |η| < r}
  have hIopen : IsOpen I := by
    simpa only [I] using isOpen_abs_lt r
  have hdx : I.EqOn (fun η => partialX γ 0 η) (fun _η : ℝ => -1) := by
    intro η hη
    exact (hdata hη).2
  simpa only [partialXY, deriv_const] using (hdx.deriv hIopen hy)

/-- Since `∂ᵧγ(0,·)` vanishes throughout the open Cauchy interval, its
derivative also vanishes there. -/
theorem partialYY_zero_of_cauchyData
    {γ : ℝ → ℝ → ℝ} {r y : ℝ} (hdata : HasCauchyDataOn γ r)
    (hy : |y| < r) : partialYY γ 0 y = 0 := by
  let I : Set ℝ := {η | |η| < r}
  have hIopen : IsOpen I := by
    simpa only [I] using isOpen_abs_lt r
  have hdy : I.EqOn (fun η => partialY γ 0 η) (fun _η : ℝ => 0) := by
    intro η hη
    exact partialY_zero_of_cauchyData hdata hη
  simpa only [partialYY, deriv_const] using (hdy.deriv hIopen hy)

/-- The actual five-component jet on the Cauchy axis is the prescribed
initial jet `(0,-1,0,0,0)`. -/
theorem jetOf_zero_eq_initialJet_of_cauchyData
    {γ : ℝ → ℝ → ℝ} {r y : ℝ} (hdata : HasCauchyDataOn γ r)
    (hy : |y| < r) : jetOf γ 0 y = initialJet := by
  have hpoint := hdata hy
  have hdy := partialY_zero_of_cauchyData hdata hy
  have hdxy := partialXY_zero_of_cauchyData hdata hy
  have hdyy := partialYY_zero_of_cauchyData hdata hy
  simp [jetOf, initialJet, hpoint.1, hpoint.2, hdy, hdxy, hdyy]

/-- The initial jet gives the correct transverse-coordinate dependence
`Γ₀(0,y) = -2 + y²` along the Cauchy surface. -/
theorem gamma0_jetOf_cauchyData
    {γ : ℝ → ℝ → ℝ} {r y : ℝ} (hdata : HasCauchyDataOn γ r)
    (hy : |y| < r) : gamma0 y (jetOf γ 0 y) = -2 + y ^ 2 := by
  rw [jetOf_zero_eq_initialJet_of_cauchyData hdata hy]
  simp [gamma0, gamma2, initialJet]

/-- In particular, `Γ₀(0,0) = -2` at the origin. -/
theorem gamma0_origin_of_cauchyData
    {γ : ℝ → ℝ → ℝ} {r : ℝ} (hdata : HasCauchyDataOn γ r)
    (hr : 0 < r) : gamma0 0 (jetOf γ 0 0) = -2 := by
  have hzero : |(0 : ℝ)| < r := by simpa using hr
  simpa using gamma0_jetOf_cauchyData hdata hzero

end

end StressTensor
