import StressTensor.Definitions

/-!
# Reflection symmetry of the auxiliary equation

For the reflection `y ↦ -y`, the first `y`-derivatives of an even candidate
change sign and the second `y`-derivative does not.  The same parity rule
applies to the `t`-derivative of the scalar function `S̃`.  This file records
the resulting algebraic invariance of the residual and its normal form.
-/

namespace StressTensor

noncomputable section

/-- Reflection of the five-jet associated with `γ̄(x,y) = γ(x,-y)`. -/
def reflectJet (z : Jet) : Jet where
  val := z.val
  dx := z.dx
  dy := -z.dy
  dxy := -z.dxy
  dyy := z.dyy

@[simp] theorem reflectJet_val (z : Jet) : (reflectJet z).val = z.val := rfl

@[simp] theorem reflectJet_dx (z : Jet) : (reflectJet z).dx = z.dx := rfl

@[simp] theorem reflectJet_dy (z : Jet) : (reflectJet z).dy = -z.dy := rfl

@[simp] theorem reflectJet_dxy (z : Jet) : (reflectJet z).dxy = -z.dxy := rfl

@[simp] theorem reflectJet_dyy (z : Jet) : (reflectJet z).dyy = z.dyy := rfl

@[simp] theorem reflectJet_involutive (z : Jet) : reflectJet (reflectJet z) = z := by
  cases z
  simp [reflectJet]

/-- Reflection of `(S̃, ∂ₜS̃, ∂_dS̃)` for an even function of `t`. -/
def reflectScalar (a : ScalarData) : ScalarData where
  S := a.S
  dSdt := -a.dSdt
  dSdd := a.dSdd

@[simp] theorem reflectScalar_S (a : ScalarData) : (reflectScalar a).S = a.S := rfl

@[simp] theorem reflectScalar_dSdt (a : ScalarData) :
    (reflectScalar a).dSdt = -a.dSdt := rfl

@[simp] theorem reflectScalar_dSdd (a : ScalarData) :
    (reflectScalar a).dSdd = a.dSdd := rfl

@[simp] theorem reflectScalar_involutive (a : ScalarData) :
    reflectScalar (reflectScalar a) = a := by
  cases a
  simp [reflectScalar]

/-! ## Parity of the auxiliary quantities -/

@[simp] theorem gamma1_reflect (y : ℝ) (z : Jet) :
    gamma1 (-y) (reflectJet z) = gamma1 y z := by
  simp [gamma1]

@[simp] theorem gamma2_reflect (y : ℝ) (z : Jet) :
    gamma2 (-y) (reflectJet z) = gamma2 y z := by
  simp [gamma2]

@[simp] theorem gamma0_reflect (y : ℝ) (z : Jet) :
    gamma0 (-y) (reflectJet z) = gamma0 y z := by
  simp [gamma0]

@[simp] theorem coeff0_reflect (y : ℝ) (z : Jet) (a : ScalarData) :
    coeff0 (-y) (reflectJet z) (reflectScalar a) = coeff0 y z a := by
  simp [coeff0]

@[simp] theorem coeff1_reflect (y : ℝ) (z : Jet) (a : ScalarData) :
    coeff1 (-y) (reflectJet z) (reflectScalar a) = -coeff1 y z a := by
  simp [coeff1]

@[simp] theorem coeff2_reflect (y : ℝ) (z : Jet) (a : ScalarData) :
    coeff2 (-y) (reflectJet z) (reflectScalar a) = coeff2 y z a := by
  simp [coeff2]

@[simp] theorem lowerOrder_reflect
    (P : Params) (y : ℝ) (z : Jet) (a : ScalarData) :
    lowerOrder P (-y) (reflectJet z) (reflectScalar a) =
      lowerOrder P y z a := by
  simp only [lowerOrder, gamma1_reflect, gamma2_reflect, reflectScalar_S,
    reflectScalar_dSdd, reflectScalar_dSdt, reflectJet_dx, reflectJet_dy,
    neg_sq]
  ring

@[simp] theorem residualNormal_reflect
    (P : Params) (y : ℝ) (z : Jet) (dxx : ℝ) (a : ScalarData) :
    residualNormal P (-y) (reflectJet z) dxx (reflectScalar a) =
      residualNormal P y z dxx a := by
  simp only [residualNormal, coeff0_reflect, coeff1_reflect, coeff2_reflect,
    lowerOrder_reflect, reflectJet_dxy, reflectJet_dyy]
  ring

@[simp] theorem normalForm_reflect
    (P : Params) (y : ℝ) (z : Jet) (a : ScalarData) :
    normalForm P (-y) (reflectJet z) (reflectScalar a) =
      normalForm P y z a := by
  simp only [normalForm, coeff0_reflect, coeff1_reflect, coeff2_reflect,
    lowerOrder_reflect, reflectJet_dxy, reflectJet_dyy]
  ring

/-! ## Reflection preserves the finite-dimensional domains -/

@[simp] theorem inQ_reflect_iff (P : Params) (x y : ℝ) :
    InQ P x (-y) ↔ InQ P x y := by
  simp [InQ]

@[simp] theorem inU_reflect_iff (P : Params) (x y : ℝ) (z : Jet) :
    InU P x (-y) (reflectJet z) ↔ InU P x y z := by
  simp [InU]

@[simp] theorem inV_reflect_iff (P : Params) (t d : ℝ) :
    InV P (-t) d ↔ InV P t d := by
  simp [InV]

end

end StressTensor
