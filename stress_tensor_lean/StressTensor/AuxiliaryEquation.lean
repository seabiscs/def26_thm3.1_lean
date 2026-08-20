import StressTensor.Definitions

/-!
# The expanded auxiliary equation

This file records the algebraic part of the divergence computation in
equations (3.13)--(3.16).  The values and first partial derivatives of
`S̃` are represented by `ScalarData`; no analytic properties of `S̃` are
needed for these polynomial identities.
-/

namespace StressTensor

noncomputable section

/-- The fully expanded expression for `∂ₓ (S Γ₁)` in (3.13). -/
def xDerivativeExpansion (y : ℝ) (z : Jet) (dxx : ℝ) (a : ScalarData) : ℝ :=
  (y ^ 2 * a.S + 2 * gamma1 y z ^ 2 * a.dSdd) * dxx
    + 4 * y * gamma1 y z * gamma2 y z * a.dSdd * z.dxy
    + 8 * gamma1 y z * gamma2 y z * a.dSdd * z.dx

/-- The fully expanded expression for `2y ∂ᵧ (S Γ₂)` in (3.14). -/
def yDerivativeExpansion (y : ℝ) (z : Jet) (a : ScalarData) : ℝ :=
  (y ^ 2 * a.S + 8 * y ^ 2 * gamma2 y z ^ 2 * a.dSdd) * z.dyy
    + 4 * y * gamma1 y z * gamma2 y z * a.dSdd * z.dxy
    + (3 * y * a.S + 24 * y * gamma2 y z ^ 2 * a.dSdd) * z.dy
    + 4 * y ^ 2 * gamma2 y z * a.dSdd * z.dx ^ 2
    + 2 * y * gamma2 y z * a.dSdt

/-- Equation (3.12), with its two derivative terms replaced by (3.13)--(3.14). -/
def residualExpanded
    (P : Params) (y : ℝ) (z : Jet) (dxx : ℝ) (a : ScalarData) : ℝ :=
  xDerivativeExpansion y z dxx a
    + 2 * (1 - 2 / P.p) * a.S * gamma2 y z
    + yDerivativeExpansion y z a

/-- Regrouping (3.13)--(3.14) gives exactly (3.15), with coefficients (3.16). -/
theorem residualExpanded_eq_residualNormal
    (P : Params) (y : ℝ) (z : Jet) (dxx : ℝ) (a : ScalarData) :
    residualExpanded P y z dxx a = residualNormal P y z dxx a := by
  simp only [residualExpanded, xDerivativeExpansion, yDerivativeExpansion,
    residualNormal, coeff0, coeff1, coeff2, lowerOrder]
  ring

/-- If the equation is noncharacteristic, its vanishing is equivalent to CK normal form. -/
theorem residualNormal_eq_zero_iff
    (P : Params) (y : ℝ) (z : Jet) (dxx : ℝ) (a : ScalarData)
    (hcoeff0 : coeff0 y z a ≠ 0) :
    residualNormal P y z dxx a = 0 ↔ dxx = normalForm P y z a := by
  unfold residualNormal normalForm
  rw [eq_div_iff hcoeff0]
  constructor <;> intro h <;> nlinarith

/-! ## Structural simplifications on the axis `y = 0` -/

@[simp] theorem gamma1_zero (z : Jet) : gamma1 0 z = 1 := by
  simp [gamma1]

@[simp] theorem gamma2_zero (z : Jet) : gamma2 0 z = z.val := by
  simp [gamma2]

@[simp] theorem coeff0_zero (z : Jet) (a : ScalarData) :
    coeff0 0 z a = 2 * a.dSdd := by
  simp [coeff0]

@[simp] theorem coeff1_zero (z : Jet) (a : ScalarData) :
    coeff1 0 z a = 0 := by
  simp [coeff1]

@[simp] theorem coeff2_zero (z : Jet) (a : ScalarData) :
    coeff2 0 z a = 0 := by
  simp [coeff2]

@[simp] theorem lowerOrder_zero (P : Params) (z : Jet) (a : ScalarData) :
    lowerOrder P 0 z a =
      8 * z.val * a.dSdd * z.dx
        + 2 * (1 - 2 / P.p) * a.S * z.val := by
  simp [lowerOrder]

end

end StressTensor
