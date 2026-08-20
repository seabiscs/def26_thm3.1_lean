import StressTensor.AnalyticInterface
import StressTensor.ScalarDerivatives
import StressTensor.AuxiliaryEquation
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Ring

/-!
# Differential bridge for the auxiliary equation

The finite-dimensional formulas in `AuxiliaryEquation` use a jet and the two
partial derivatives of `S̃` as independent scalar data.  This file connects
those formulas to actual one-variable derivatives of a two-variable function
`γ`.  All differentiability and mixed-partial assumptions used by the chain
rule are explicit theorem hypotheses.
-/

namespace StressTensor

noncomputable section

/-! ## Actual fields attached to a function -/

/-- The actual field `Γ₁[γ]`. -/
def gamma1Field (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  gamma1 y (jetOf γ x y)

/-- The actual field `Γ₂[γ]`. -/
def gamma2Field (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  gamma2 y (jetOf γ x y)

/-- The actual field `Γ₀[γ]`. -/
def gamma0Field (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  gamma0 y (jetOf γ x y)

/-- The scalar data of `S̃` evaluated along `(y, Γ₀[γ])`. -/
def scalarDataField (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ScalarData :=
  scalarDataOfJet P y (jetOf γ x y)

/-- The actual composed field `S[γ](x,y) = S̃(y, Γ₀[γ](x,y))`. -/
def scalarField (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  (scalarDataField P γ x y).S

/-- `S̃` regarded as a function on the product of its two scalar variables. -/
def stildeUncurried (P : Params) : ℝ × ℝ → ℝ :=
  fun w => Stilde P w.1 w.2

/-- The differential encoded by the two partials stored in `ScalarData`. -/
def scalarDifferential (a : ScalarData) : (ℝ × ℝ) →L[ℝ] ℝ :=
  a.dSdt • ContinuousLinearMap.fst ℝ ℝ ℝ +
    a.dSdd • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem scalarDifferential_apply (a : ScalarData) (v : ℝ × ℝ) :
    scalarDifferential a v = a.dSdt * v.1 + a.dSdd * v.2 := by
  simp [scalarDifferential]

@[simp] theorem scalarField_eq_Stilde
    (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) :
    scalarField P γ x y = Stilde P y (gamma0Field γ x y) := by
  rfl

/-! ## Derivatives of `Γ₁`, `Γ₂`, and `Γ₀` -/

/-- The derivative of `Γ₁[γ]` in the `x` direction. -/
theorem hasDerivAt_gamma1Field_x
    {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hxx : HasDerivAt (fun ξ => partialX γ ξ y) (partialXX γ x y) x) :
    HasDerivAt (fun ξ => gamma1Field γ ξ y)
      (y ^ 2 * partialXX γ x y) x := by
  have h := (hxx.const_mul (y ^ 2)).const_add 1
  simpa [gamma1Field, gamma1, jetOf] using h

/-- The derivative of `Γ₂[γ]` in `x`; `hyx` explicitly supplies
the equality of the two mixed derivatives at the point. -/
theorem hasDerivAt_gamma2Field_x
    {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hx : HasDerivAt (fun ξ => γ ξ y) (partialX γ x y) x)
    (hyx : HasDerivAt (fun ξ => partialY γ ξ y) (partialXY γ x y) x) :
    HasDerivAt (fun ξ => gamma2Field γ ξ y)
      (partialX γ x y + y * partialXY γ x y / 2) x := by
  have hpart := (hyx.const_mul y).div_const 2
  have heq : partialX γ x y + y * partialXY γ x y / 2 =
      partialX γ x y + (y * partialXY γ x y) / 2 := by ring
  change HasDerivAt
    ((fun ξ => γ ξ y) + fun ξ => y * partialY γ ξ y / 2)
    (partialX γ x y + y * partialXY γ x y / 2) x
  rw [heq]
  exact HasDerivAt.add hx hpart

/-- The polynomial rate `∂ₓΓ₀` occurring in (3.13). -/
def gamma0XRate (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  2 * partialXX γ x y * gamma1Field γ x y +
    8 * gamma2Field γ x y *
      (partialX γ x y + y * partialXY γ x y / 2)

/-- The actual `x` derivative of `Γ₀[γ]`. -/
theorem hasDerivAt_gamma0Field_x
    {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hx : HasDerivAt (fun ξ => γ ξ y) (partialX γ x y) x)
    (hxx : HasDerivAt (fun ξ => partialX γ ξ y) (partialXX γ x y) x)
    (hyx : HasDerivAt (fun ξ => partialY γ ξ y) (partialXY γ x y) x) :
    HasDerivAt (fun ξ => gamma0Field γ ξ y) (gamma0XRate γ x y) x := by
  have hdx := hxx
  have hg2 := hasDerivAt_gamma2Field_x hx hyx
  have h := ((hdx.const_mul 2).add ((hdx.fun_pow 2).const_mul (y ^ 2))).add
    ((hg2.fun_pow 2).const_mul 4)
  apply h.congr_deriv
  simp only [gamma0XRate, jetOf, gamma1Field, gamma2Field, gamma1]
  ring

/-- The derivative of `Γ₁[γ]` in the `y` direction. -/
theorem hasDerivAt_gamma1Field_y
    {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hxy : HasDerivAt (fun η => partialX γ x η) (partialXY γ x y) y) :
    HasDerivAt (fun η => gamma1Field γ x η)
      (2 * y * partialX γ x y + y ^ 2 * partialXY γ x y) y := by
  have h := (hasDerivAt_pow 2 y).mul hxy
  have h' := h.const_add 1
  apply h'.congr_deriv
  ring

/-- The derivative of `Γ₂[γ]` in the `y` direction. -/
theorem hasDerivAt_gamma2Field_y
    {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hy : HasDerivAt (γ x) (partialY γ x y) y)
    (hyy : HasDerivAt (fun η => partialY γ x η) (partialYY γ x y) y) :
    HasDerivAt (fun η => gamma2Field γ x η)
      ((3 * partialY γ x y + y * partialYY γ x y) / 2) y := by
  have hprod := (hasDerivAt_id' y).mul hyy
  have h := hy.add (hprod.div_const 2)
  apply h.congr_deriv
  ring

/-- The polynomial rate `∂ᵧΓ₀` occurring in (3.14). -/
def gamma0YRate (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  2 * partialXY γ x y + 2 * y * partialX γ x y ^ 2 +
    2 * y ^ 2 * partialX γ x y * partialXY γ x y +
    4 * gamma2Field γ x y *
      (3 * partialY γ x y + y * partialYY γ x y)

/-- The actual `y` derivative of `Γ₀[γ]`. -/
theorem hasDerivAt_gamma0Field_y
    {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hy : HasDerivAt (γ x) (partialY γ x y) y)
    (hxy : HasDerivAt (fun η => partialX γ x η) (partialXY γ x y) y)
    (hyy : HasDerivAt (fun η => partialY γ x η) (partialYY γ x y) y) :
    HasDerivAt (fun η => gamma0Field γ x η) (gamma0YRate γ x y) y := by
  have hdx := hxy
  have hg2 := hasDerivAt_gamma2Field_y hy hyy
  have hfirst := hdx.const_mul 2
  have hmiddle := (hasDerivAt_pow 2 y).mul (hdx.fun_pow 2)
  have hlast := (hg2.fun_pow 2).const_mul 4
  have h := (hfirst.add hmiddle).add hlast
  apply h.congr_deriv
  simp only [gamma0YRate, jetOf, gamma2Field]
  ring

/-! ## The two-variable chain rule for `S̃` -/

/-- Composing the full differential of `S̃` with the `x` path gives
`Sₓ = S̃_d ∂ₓΓ₀`. -/
theorem hasDerivAt_scalarField_x_of_gamma0
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y gx : ℝ}
    (hgamma0 : HasDerivAt (fun ξ => gamma0Field γ ξ y) gx x)
    (hS : HasFDerivAt (stildeUncurried P)
      (scalarDifferential (scalarDataField P γ x y))
      (y, gamma0Field γ x y)) :
    HasDerivAt (fun ξ => scalarField P γ ξ y)
      ((scalarDataField P γ x y).dSdd * gx) x := by
  have hconst : HasDerivAt (fun _ : ℝ => y) 0 x := hasDerivAt_const x y
  have hpath := hconst.prodMk hgamma0
  have hcomp := hS.comp_hasDerivAt x hpath
  have hvalue :
      scalarDifferential (scalarDataField P γ x y) (0, gx) =
        (scalarDataField P γ x y).dSdd * gx := by simp
  apply hcomp.congr_deriv hvalue

/-- Composing the full differential of `S̃` with the `y` path gives
`Sᵧ = S̃_t + S̃_d ∂ᵧΓ₀`. -/
theorem hasDerivAt_scalarField_y_of_gamma0
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y gy : ℝ}
    (hgamma0 : HasDerivAt (fun η => gamma0Field γ x η) gy y)
    (hS : HasFDerivAt (stildeUncurried P)
      (scalarDifferential (scalarDataField P γ x y))
      (y, gamma0Field γ x y)) :
    HasDerivAt (fun η => scalarField P γ x η)
      ((scalarDataField P γ x y).dSdt +
        (scalarDataField P γ x y).dSdd * gy) y := by
  have hid : HasDerivAt (fun η : ℝ => η) 1 y := hasDerivAt_id y
  have hpath := hid.prodMk hgamma0
  have hcomp := hS.comp_hasDerivAt y hpath
  have hvalue :
      scalarDifferential (scalarDataField P γ x y) (1, gy) =
        (scalarDataField P γ x y).dSdt +
          (scalarDataField P γ x y).dSdd * gy := by simp
  apply hcomp.congr_deriv hvalue

/-! ## Product-rule expansions (3.13)--(3.14) -/

/-- Equation (3.13) for the actual fields attached to `γ`. -/
theorem hasDerivAt_scalar_mul_gamma1_x
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hx : HasDerivAt (fun ξ => γ ξ y) (partialX γ x y) x)
    (hxx : HasDerivAt (fun ξ => partialX γ ξ y) (partialXX γ x y) x)
    (hyx : HasDerivAt (fun ξ => partialY γ ξ y) (partialXY γ x y) x)
    (hS : HasFDerivAt (stildeUncurried P)
      (scalarDifferential (scalarDataField P γ x y))
      (y, gamma0Field γ x y)) :
    HasDerivAt
      (fun ξ => scalarField P γ ξ y * gamma1Field γ ξ y)
      (xDerivativeExpansion y (jetOf γ x y) (partialXX γ x y)
        (scalarDataField P γ x y)) x := by
  have hg0 := hasDerivAt_gamma0Field_x hx hxx hyx
  have hscalar := hasDerivAt_scalarField_x_of_gamma0 hg0 hS
  have hg1 := hasDerivAt_gamma1Field_x hxx
  have hprod := hscalar.mul hg1
  apply hprod.congr_deriv
  simp only [xDerivativeExpansion, gamma0XRate, gamma1Field, gamma2Field,
    scalarField, scalarDataField, scalarDataOfJet, scalarDataAt, jetOf]
  ring

/-- The unscaled derivative in (3.14); multiplication by `2y` is recorded
in `two_y_mul_yProductRate`. -/
def yProductRate
    (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  ((scalarDataField P γ x y).dSdt +
      (scalarDataField P γ x y).dSdd * gamma0YRate γ x y) *
      gamma2Field γ x y +
    scalarField P γ x y *
      ((3 * partialY γ x y + y * partialYY γ x y) / 2)

/-- The product rule for `∂ᵧ(S[γ] Γ₂[γ])`. -/
theorem hasDerivAt_scalar_mul_gamma2_y
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hy : HasDerivAt (γ x) (partialY γ x y) y)
    (hxy : HasDerivAt (fun η => partialX γ x η) (partialXY γ x y) y)
    (hyy : HasDerivAt (fun η => partialY γ x η) (partialYY γ x y) y)
    (hS : HasFDerivAt (stildeUncurried P)
      (scalarDifferential (scalarDataField P γ x y))
      (y, gamma0Field γ x y)) :
    HasDerivAt
      (fun η => scalarField P γ x η * gamma2Field γ x η)
      (yProductRate P γ x y) y := by
  have hg0 := hasDerivAt_gamma0Field_y hy hxy hyy
  have hscalar := hasDerivAt_scalarField_y_of_gamma0 hg0 hS
  have hg2 := hasDerivAt_gamma2Field_y hy hyy
  exact hscalar.mul hg2

/-- Multiplying the preceding derivative by `2y` gives precisely the
expanded expression in (3.14), including at `y = 0`. -/
theorem two_y_mul_yProductRate
    (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) :
    2 * y * yProductRate P γ x y =
      yDerivativeExpansion y (jetOf γ x y) (scalarDataField P γ x y) := by
  simp only [yProductRate, yDerivativeExpansion, gamma0YRate, gamma2Field,
    scalarField, scalarDataField, scalarDataOfJet, scalarDataAt,
    jetOf, gamma1]
  ring

/-- A direct `deriv` form of (3.14). -/
theorem two_y_mul_deriv_scalar_mul_gamma2
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hy : HasDerivAt (γ x) (partialY γ x y) y)
    (hxy : HasDerivAt (fun η => partialX γ x η) (partialXY γ x y) y)
    (hyy : HasDerivAt (fun η => partialY γ x η) (partialYY γ x y) y)
    (hS : HasFDerivAt (stildeUncurried P)
      (scalarDifferential (scalarDataField P γ x y))
      (y, gamma0Field γ x y)) :
    2 * y * deriv
        (fun η => scalarField P γ x η * gamma2Field γ x η) y =
      yDerivativeExpansion y (jetOf γ x y) (scalarDataField P γ x y) := by
  rw [(hasDerivAt_scalar_mul_gamma2_y hy hxy hyy hS).deriv]
  exact two_y_mul_yProductRate P γ x y

/-! ## The actual residual -/

/-- Equation (3.12) interpreted using actual derivatives. -/
def differentialResidual
    (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun ξ => scalarField P γ ξ y * gamma1Field γ ξ y) x +
    2 * (1 - 2 / P.p) * scalarField P γ x y * gamma2Field γ x y +
    2 * y * deriv
      (fun η => scalarField P γ x η * gamma2Field γ x η) y

/-- Equations (3.12)--(3.15): the actual differential residual is exactly
the jet-level polynomial residual. -/
theorem differentialResidual_eq_residualNormal
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hx : HasDerivAt (fun ξ => γ ξ y) (partialX γ x y) x)
    (hxx : HasDerivAt (fun ξ => partialX γ ξ y) (partialXX γ x y) x)
    (hyx : HasDerivAt (fun ξ => partialY γ ξ y) (partialXY γ x y) x)
    (hy : HasDerivAt (γ x) (partialY γ x y) y)
    (hxy : HasDerivAt (fun η => partialX γ x η) (partialXY γ x y) y)
    (hyy : HasDerivAt (fun η => partialY γ x η) (partialYY γ x y) y)
    (hS : HasFDerivAt (stildeUncurried P)
      (scalarDifferential (scalarDataField P γ x y))
      (y, gamma0Field γ x y)) :
    differentialResidual P γ x y =
      residualNormal P y (jetOf γ x y) (partialXX γ x y)
        (scalarDataField P γ x y) := by
  have hxprod := hasDerivAt_scalar_mul_gamma1_x hx hxx hyx hS
  have hyprod := hasDerivAt_scalar_mul_gamma2_y hy hxy hyy hS
  calc
    differentialResidual P γ x y =
        residualExpanded P y (jetOf γ x y) (partialXX γ x y)
          (scalarDataField P γ x y) := by
      rw [differentialResidual, hxprod.deriv, hyprod.deriv,
        two_y_mul_yProductRate P γ x y]
      rfl
    _ = residualNormal P y (jetOf γ x y) (partialXX γ x y)
          (scalarDataField P γ x y) :=
      residualExpanded_eq_residualNormal P y (jetOf γ x y)
        (partialXX γ x y) (scalarDataField P γ x y)

/-- Under the same explicit calculus hypotheses, vanishing of the actual
residual is precisely `auxiliaryEquationAt`. -/
theorem differentialResidual_eq_zero_iff_auxiliaryEquationAt
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hx : HasDerivAt (fun ξ => γ ξ y) (partialX γ x y) x)
    (hxx : HasDerivAt (fun ξ => partialX γ ξ y) (partialXX γ x y) x)
    (hyx : HasDerivAt (fun ξ => partialY γ ξ y) (partialXY γ x y) x)
    (hy : HasDerivAt (γ x) (partialY γ x y) y)
    (hxy : HasDerivAt (fun η => partialX γ x η) (partialXY γ x y) y)
    (hyy : HasDerivAt (fun η => partialY γ x η) (partialYY γ x y) y)
    (hS : HasFDerivAt (stildeUncurried P)
      (scalarDifferential (scalarDataField P γ x y))
      (y, gamma0Field γ x y)) :
    differentialResidual P γ x y = 0 ↔ auxiliaryEquationAt P γ x y := by
  rw [differentialResidual_eq_residualNormal hx hxx hyx hy hxy hyy hS]
  rfl

/-! ## The singular stress field off the light line -/

/-- The singular denominator `|y|^(2/p)` in (3.10). -/
def singularDenominator (P : Params) (y : ℝ) : ℝ :=
  Real.rpow |y| (2 / P.p)

/-- The first component of the factored stress field in (3.10). -/
def singularStressX
    (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  scalarField P γ x y * gamma1Field γ x y / singularDenominator P y

/-- The second component of the factored stress field in (3.10). -/
def singularStressY
    (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  2 * ((y / singularDenominator P y) *
    (scalarField P γ x y * gamma2Field γ x y))

/-- The ordinary two-dimensional divergence of the factored stress. -/
def singularStressDivergence
    (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun ξ => singularStressX P γ ξ y) x +
    deriv (fun η => singularStressY P γ x η) y

/-- The derivative needed for the singular `y` component.  It is valid for
every real exponent and every `y ≠ 0`. -/
theorem hasDerivAt_id_div_abs_rpow
    (a : ℝ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun η : ℝ => η / Real.rpow |η| a)
      ((1 - a) / Real.rpow |y| a) y := by
  have habs : HasDerivAt (fun η : ℝ => |η|) (SignType.sign y : ℝ) y :=
    hasDerivAt_abs hy
  have hpow := habs.rpow_const (p := a) (Or.inl (abs_ne_zero.mpr hy))
  have hpow0 : Real.rpow |y| a ≠ 0 :=
    (Real.rpow_pos_of_pos (abs_pos.mpr hy) a).ne'
  have hraw := (hasDerivAt_id y).fun_div hpow hpow0
  have hmul : |y| * |y| ^ (a - 1) = |y| ^ a := by
    calc
      |y| * |y| ^ (a - 1) = |y| ^ (1 : ℝ) * |y| ^ (a - 1) :=
        congrArg (fun r => r * |y| ^ (a - 1)) (Real.rpow_one |y|).symm
      _ = |y| ^ ((1 : ℝ) + (a - 1)) :=
        (Real.rpow_add (abs_pos.mpr hy) 1 (a - 1)).symm
      _ = |y| ^ a := by congr 1; ring
  apply hraw.congr_deriv
  simp only [Real.rpow_eq_pow]
  field_simp [hpow0]
  simp only [id_eq]
  have hsign : y * (SignType.sign y : ℝ) = |y| := by
    rw [mul_comm, sign_mul_self]
  rw [hsign]
  rw [show |y| * a * |y| ^ (a - 1) =
      a * (|y| * |y| ^ (a - 1)) by ring, hmul]
  ring

/-- The `x` derivative of the first singular stress component. -/
theorem hasDerivAt_singularStressX_x
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hx : HasDerivAt (fun ξ => γ ξ y) (partialX γ x y) x)
    (hxx : HasDerivAt (fun ξ => partialX γ ξ y) (partialXX γ x y) x)
    (hyx : HasDerivAt (fun ξ => partialY γ ξ y) (partialXY γ x y) x)
    (hS : HasFDerivAt (stildeUncurried P)
      (scalarDifferential (scalarDataField P γ x y))
      (y, gamma0Field γ x y)) :
    HasDerivAt (fun ξ => singularStressX P γ ξ y)
      (xDerivativeExpansion y (jetOf γ x y) (partialXX γ x y)
        (scalarDataField P γ x y) / singularDenominator P y) x := by
  simpa only [singularStressX] using
    (hasDerivAt_scalar_mul_gamma1_x hx hxx hyx hS).div_const
      (singularDenominator P y)

/-- The `y` derivative of the second singular stress component. -/
theorem hasDerivAt_singularStressY_y
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ} (hy0 : y ≠ 0)
    (hy : HasDerivAt (γ x) (partialY γ x y) y)
    (hxy : HasDerivAt (fun η => partialX γ x η) (partialXY γ x y) y)
    (hyy : HasDerivAt (fun η => partialY γ x η) (partialYY γ x y) y)
    (hS : HasFDerivAt (stildeUncurried P)
      (scalarDifferential (scalarDataField P γ x y))
      (y, gamma0Field γ x y)) :
    HasDerivAt (fun η => singularStressY P γ x η)
      (2 * (((1 - 2 / P.p) / singularDenominator P y) *
          (scalarField P γ x y * gamma2Field γ x y) +
        (y / singularDenominator P y) * yProductRate P γ x y)) y := by
  have hw := hasDerivAt_id_div_abs_rpow (2 / P.p) hy0
  have hproduct := hasDerivAt_scalar_mul_gamma2_y hy hxy hyy hS
  have h := (hw.mul hproduct).const_mul 2
  simpa only [singularStressY, singularDenominator, Pi.mul_apply] using h

/-- Off the light line, divergence of the singular stress is the actual
residual divided by `|y|^(2/p)`. -/
theorem singularStressDivergence_eq_residual_div
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ} (hy0 : y ≠ 0)
    (hx : HasDerivAt (fun ξ => γ ξ y) (partialX γ x y) x)
    (hxx : HasDerivAt (fun ξ => partialX γ ξ y) (partialXX γ x y) x)
    (hyx : HasDerivAt (fun ξ => partialY γ ξ y) (partialXY γ x y) x)
    (hy : HasDerivAt (γ x) (partialY γ x y) y)
    (hxy : HasDerivAt (fun η => partialX γ x η) (partialXY γ x y) y)
    (hyy : HasDerivAt (fun η => partialY γ x η) (partialYY γ x y) y)
    (hS : HasFDerivAt (stildeUncurried P)
      (scalarDifferential (scalarDataField P γ x y))
      (y, gamma0Field γ x y)) :
    singularStressDivergence P γ x y =
      differentialResidual P γ x y / singularDenominator P y := by
  have hdenom : singularDenominator P y ≠ 0 := by
    exact (Real.rpow_pos_of_pos (abs_pos.mpr hy0) (2 / P.p)).ne'
  have hxstress := hasDerivAt_singularStressX_x hx hxx hyx hS
  have hystress := hasDerivAt_singularStressY_y hy0 hy hxy hyy hS
  have hxproduct := hasDerivAt_scalar_mul_gamma1_x hx hxx hyx hS
  have hyproduct := hasDerivAt_scalar_mul_gamma2_y hy hxy hyy hS
  simp only [singularStressDivergence, differentialResidual]
  rw [hxstress.deriv, hystress.deriv, hxproduct.deriv, hyproduct.deriv]
  field_simp [hdenom]
  ring

/-- Equation (3.11) in the displayed `|y|^(-2/p)` form. -/
theorem singularStressDivergence_eq_rpow_mul_residual
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ} (hy0 : y ≠ 0)
    (hx : HasDerivAt (fun ξ => γ ξ y) (partialX γ x y) x)
    (hxx : HasDerivAt (fun ξ => partialX γ ξ y) (partialXX γ x y) x)
    (hyx : HasDerivAt (fun ξ => partialY γ ξ y) (partialXY γ x y) x)
    (hy : HasDerivAt (γ x) (partialY γ x y) y)
    (hxy : HasDerivAt (fun η => partialX γ x η) (partialXY γ x y) y)
    (hyy : HasDerivAt (fun η => partialY γ x η) (partialYY γ x y) y)
    (hS : HasFDerivAt (stildeUncurried P)
      (scalarDifferential (scalarDataField P γ x y))
      (y, gamma0Field γ x y)) :
    singularStressDivergence P γ x y =
      Real.rpow |y| (-(2 / P.p)) * differentialResidual P γ x y := by
  rw [singularStressDivergence_eq_residual_div hy0 hx hxx hyx hy hxy hyy hS]
  rw [singularDenominator, div_eq_mul_inv]
  have hinv : (Real.rpow |y| (2 / P.p))⁻¹ =
      Real.rpow |y| (-(2 / P.p)) := by
    simpa only [Real.rpow_eq_pow] using
      (Real.rpow_neg (abs_nonneg y) (2 / P.p)).symm
  rw [hinv]
  ring

/-- Combining (3.11) with (3.15) gives the divergence directly in terms of
the normal polynomial residual. -/
theorem singularStressDivergence_eq_rpow_mul_residualNormal
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ} (hy0 : y ≠ 0)
    (hx : HasDerivAt (fun ξ => γ ξ y) (partialX γ x y) x)
    (hxx : HasDerivAt (fun ξ => partialX γ ξ y) (partialXX γ x y) x)
    (hyx : HasDerivAt (fun ξ => partialY γ ξ y) (partialXY γ x y) x)
    (hy : HasDerivAt (γ x) (partialY γ x y) y)
    (hxy : HasDerivAt (fun η => partialX γ x η) (partialXY γ x y) y)
    (hyy : HasDerivAt (fun η => partialY γ x η) (partialYY γ x y) y)
    (hS : HasFDerivAt (stildeUncurried P)
      (scalarDifferential (scalarDataField P γ x y))
      (y, gamma0Field γ x y)) :
    singularStressDivergence P γ x y =
      Real.rpow |y| (-(2 / P.p)) *
        residualNormal P y (jetOf γ x y) (partialXX γ x y)
          (scalarDataField P γ x y) := by
  rw [singularStressDivergence_eq_rpow_mul_residual hy0 hx hxx hyx hy hxy hyy hS]
  rw [differentialResidual_eq_residualNormal hx hxx hyx hy hxy hyy hS]

end


end StressTensor
