import StressTensor.ScalarNeighborhood
import StressTensor.ActualFieldBridge
import StressTensor.AnalyticInterface

/-!
# Localization bridges for the stress-tensor ansatz

This module transfers the unconditional scalar estimates on `V_q` to the
jet neighborhood `U_q`.  It then packages the corresponding
noncharacteristic bound and the actual-gradient consequences for a
differentiable ansatz.
-/

namespace StressTensor

noncomputable section

/-! ## Scalar estimates after composition with the jet -/

/-- The base of every real power in the composed scalar factors is positive
on `U_q`. -/
theorem composedBase_pos_of_inU
    {P : Params} {x y : ℝ} {z : Jet} (hU : InU P x y z) :
    0 < 1 + y ^ 2 * gamma0 y z := by
  exact (inV_gamma0_of_inU hU).base_pos

/-- The two-sided estimate for the composed deficit factor. -/
theorem Ccomp_bounds_of_inU
    {P : Params} {x y : ℝ} {z : Jet} (hU : InU P x y z) :
    (1 : ℝ) / 4 < Ccomp P y z ∧ Ccomp P y z < 4 := by
  simpa only [Ccomp] using (inV_gamma0_of_inU hU).Ctilde_bounds

/-- Positivity of the composed deficit factor, with no extra scalar
hypothesis. -/
theorem Ccomp_pos_of_inU
    {P : Params} {x y : ℝ} {z : Jet} (hU : InU P x y z) :
    0 < Ccomp P y z := by
  linarith [Ccomp_bounds_of_inU hU |>.1]

/-- The lower bound for the composed stress factor. -/
theorem one_eighth_le_Scomp_of_inU
    {P : Params} {x y : ℝ} {z : Jet} (hU : InU P x y z) :
    (1 : ℝ) / 8 ≤ Scomp P y z := by
  simpa only [Scomp] using (inV_gamma0_of_inU hU).one_eighth_le_Stilde

/-- The `S` component of `scalarDataOfJet` inherits the bound in (3.19). -/
theorem scalarDataOfJet_S_ge_of_inU
    {P : Params} {x y : ℝ} {z : Jet} (hU : InU P x y z) :
    (1 : ℝ) / 8 ≤ (scalarDataOfJet P y z).S := by
  simpa only [scalarDataOfJet, scalarDataAt]
    using (inV_gamma0_of_inU hU).one_eighth_le_Stilde

/-- The `d` derivative stored in `scalarDataOfJet` satisfies (3.20). -/
theorem scalarDataOfJet_dSdd_div_S_ge_of_inU
    {P : Params} {x y : ℝ} {z : Jet} (hU : InU P x y z) :
    (P.q - 1) / 32 ≤
      (scalarDataOfJet P y z).dSdd / (scalarDataOfJet P y z).S := by
  simpa only [scalarDataOfJet, scalarDataAt]
    using (inV_gamma0_of_inU hU).deriv_Stilde_d_div_ge_q_sub_one_div_32

/-! ## Unconditional noncharacteristic bound on `U_q` -/

/-- The leading coefficient has the claimed quantitative lower bound on
`U_q`, with all scalar estimates discharged from `InU`. -/
theorem coeff0_scalarDataOfJet_ge_of_inU
    (P : Params) {x y : ℝ} {z : Jet} (hU : InU P x y z) :
    (P.q - 1) / 1024 ≤
      coeff0 y z (scalarDataOfJet P y z) := by
  exact coeff0_ge_q_sub_one_div_1024_of_ratio P y z
    (scalarDataOfJet P y z)
    (scalarDataOfJet_S_ge_of_inU hU)
    (scalarDataOfJet_dSdd_div_S_ge_of_inU hU)
    (gamma1_ge_one_half hU)

/-- In particular, the leading coefficient is strictly positive on `U_q`. -/
theorem coeff0_scalarDataOfJet_pos_of_inU
    (P : Params) {x y : ℝ} {z : Jet} (hU : InU P x y z) :
    0 < coeff0 y z (scalarDataOfJet P y z) := by
  have hq : 0 < (P.q - 1) / 1024 := by
    exact div_pos (sub_pos.mpr P.one_lt_q) (by norm_num)
  exact lt_of_lt_of_le hq (coeff0_scalarDataOfJet_ge_of_inU P hU)

/-- The auxiliary equation is therefore in CK normal form at every point
whose actual jet belongs to `U_q`. -/
theorem auxiliaryEquation_iff_normalForm_of_inU
    (P : Params) {gamma : ℝ → ℝ → ℝ} {x y : ℝ}
    (hU : InU P x y (jetOf gamma x y)) :
    auxiliaryEquationAt P gamma x y ↔
      partialXX gamma x y = normalForm P y (jetOf gamma x y)
        (scalarDataOfJet P y (jetOf gamma x y)) := by
  exact auxiliaryEquation_iff_normalForm P gamma x y
    (coeff0_scalarDataOfJet_pos_of_inU P hU).ne'

/-! ## Function-level gradient localization -/

/-- Along the light axis, the actual gradient of the differentiable ansatz
is exactly `(1,0)`. -/
theorem actualAnsatzGradient_on_axis
    {gamma : ℝ → ℝ → ℝ} {x : ℝ}
    (hx : DifferentiableAt ℝ (fun xi => gamma xi 0) x)
    (hy : DifferentiableAt ℝ (gamma x) 0) :
    actualAnsatzGradient gamma x 0 = (1, 0) := by
  rw [actualAnsatzGradient_eq_ansatzGradient hx hy]
  exact ansatzGradient_zero (jetOf gamma x 0)

/-- Consequently, the actual gradient has squared norm one on the axis. -/
theorem normSq_actualAnsatzGradient_on_axis
    {gamma : ℝ → ℝ → ℝ} {x : ℝ}
    (hx : DifferentiableAt ℝ (fun xi => gamma xi 0) x)
    (hy : DifferentiableAt ℝ (gamma x) 0) :
    normSq (actualAnsatzGradient gamma x 0) = 1 := by
  rw [actualAnsatzGradient_on_axis hx hy]
  norm_num [normSq]

/-- Off the light axis, membership of the actual jet in `U_q` makes the
actual ansatz gradient strictly spacelike. -/
theorem normSq_actualAnsatzGradient_lt_one_of_inU
    {P : Params} {gamma : ℝ → ℝ → ℝ} {x y : ℝ}
    (hU : InU P x y (jetOf gamma x y)) (hy0 : y ≠ 0)
    (hx : DifferentiableAt ℝ (fun xi => gamma xi y) x)
    (hy : DifferentiableAt ℝ (gamma x) y) :
    normSq (actualAnsatzGradient gamma x y) < 1 := by
  rw [actualAnsatzGradient_eq_ansatzGradient hx hy]
  exact normSq_ansatz_lt_one_of_inU hU hy0

/-- A single package containing both identification of the actual gradient
and its strict spacelikeness after localization. -/
theorem actualAnsatzGradient_localized
    {P : Params} {gamma : ℝ → ℝ → ℝ} {x y : ℝ}
    (hU : InU P x y (jetOf gamma x y)) (hy0 : y ≠ 0)
    (hx : DifferentiableAt ℝ (fun xi => gamma xi y) x)
    (hy : DifferentiableAt ℝ (gamma x) y) :
    actualAnsatzGradient gamma x y = ansatzGradient y (jetOf gamma x y) ∧
      normSq (actualAnsatzGradient gamma x y) < 1 := by
  exact ⟨actualAnsatzGradient_eq_ansatzGradient hx hy,
    normSq_actualAnsatzGradient_lt_one_of_inU hU hy0 hx hy⟩

/-! ## Pointwise stress factorization from localization -/

/-- Off the axis, `InU` supplies both positivity conditions required to
factor the original stress. -/
theorem stressFactorizationAdmissibleAt_of_inU
    {P : Params} {gamma : ℝ → ℝ → ℝ} {x y : ℝ}
    (hU : InU P x y (jetOf gamma x y)) (hy0 : y ≠ 0)
    (hx : DifferentiableAt ℝ (fun xi => gamma xi y) x)
    (hy : DifferentiableAt ℝ (gamma x) y) :
    StressFactorizationAdmissibleAt P gamma x y := by
  exact ⟨hx, hy, hy0, composedBase_pos_of_inU hU, Ccomp_pos_of_inU hU⟩

/-- Pointwise equality of the original and factored stress follows directly
from `InU`, differentiability, and `y ≠ 0`. -/
theorem energyGradientStress_eq_singularStress_of_inU
    {P : Params} {gamma : ℝ → ℝ → ℝ} {x y : ℝ}
    (hU : InU P x y (jetOf gamma x y)) (hy0 : y ≠ 0)
    (hx : DifferentiableAt ℝ (fun xi => gamma xi y) x)
    (hy : DifferentiableAt ℝ (gamma x) y) :
    energyGradientStress P gamma x y = singularStress P gamma x y := by
  exact energyGradientStress_eq_singularStress
    (stressFactorizationAdmissibleAt_of_inU hU hy0 hx hy)

end

end StressTensor
