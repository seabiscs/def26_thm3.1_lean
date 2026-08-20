import StressTensor.AnalyticInterface
import StressTensor.AuxiliaryEquation
import StressTensor.ScalarDerivatives

/-!
# Exact formulas on the light axis

This file specializes the scalar functions and the coefficients of the
auxiliary equation to `y = 0`.  The hypothesis `d < 0` makes
`-q d / 2` strictly positive, so all laws for its negative real powers apply
on their natural domain.
-/

namespace StressTensor

noncomputable section

/-! ## Scalar functions at `t = 0` -/

/-- The positive quantity which occurs in every axis formula. -/
theorem axisDeficit_pos (P : Params) {d : ℝ} (hd : d < 0) :
    0 < -(P.q * d) / 2 := by
  exact div_pos (neg_pos.mpr (mul_neg_of_pos_of_neg P.q_pos hd)) (by norm_num)

/-- The continued deficit on the axis. -/
theorem Ctilde_axis (P : Params) (d : ℝ) :
    Ctilde P 0 d = -(P.q * d) / 2 :=
  Ctilde_zero P d

/-- The exact axis value of `Stilde` from the manuscript. -/
theorem Stilde_axis (P : Params) {d : ℝ} (hd : d < 0) :
    Stilde P 0 d =
      Real.rpow (-(P.q * d) / 2) (-1 / P.p) := by
  exact Stilde_zero P d (axisDeficit_pos P hd)

/-- Evenness forces the `t` derivative of `Stilde` to vanish at the axis.
This identity for Mathlib's total `deriv` does not require a separate
differentiability hypothesis. -/
theorem deriv_Stilde_t_axis (P : Params) (d : ℝ) :
    deriv (fun t => Stilde P t d) 0 = 0 := by
  let f : ℝ → ℝ := fun t => Stilde P t d
  have hfun : (fun t => f (-t)) = f := by
    funext t
    exact Stilde_neg P t d
  have hderiv : deriv f 0 = -deriv f 0 := by
    calc
      deriv f 0 = deriv (fun t => f (-t)) 0 := by rw [hfun]
      _ = -deriv f (-0) := deriv_comp_neg f 0
      _ = -deriv f 0 := by norm_num
  linarith

/-- The exact `d` derivative of `Stilde` on the axis. -/
theorem deriv_Stilde_d_axis (P : Params) {d : ℝ} (hd : d < 0) :
    deriv (fun d' => Stilde P 0 d') d =
      P.q / (2 * P.p) *
        Real.rpow (-(P.q * d) / 2) (-1 - 1 / P.p) := by
  let K : ℝ := -(P.q * d) / 2
  have hK : 0 < K := by simpa only [K] using axisDeficit_pos P hd
  have hC : 0 < Ctilde P 0 d := by simpa only [Ctilde_axis] using hK
  have hbase : 0 < 1 + (0 : ℝ) ^ 2 * d := by norm_num
  have hpow :
      Real.rpow K (-1 / P.p) / K =
        Real.rpow K (-1 - 1 / P.p) := by
    calc
      Real.rpow K (-1 / P.p) / K =
          Real.rpow K (-1 / P.p) / Real.rpow K (1 : ℝ) := by
        congr 1
        exact (Real.rpow_one K).symm
      _ = Real.rpow K (-1 / P.p - 1) :=
        (Real.rpow_sub hK (-1 / P.p) 1).symm
      _ = Real.rpow K (-1 - 1 / P.p) := by
        congr 1
        ring
  calc
    deriv (fun d' => Stilde P 0 d') d =
        Stilde P 0 d * stildeDLogRate P 0 d :=
      deriv_Stilde_d P 0 d hbase hC
    _ = Real.rpow K (-1 / P.p) *
        (P.q / (2 * P.p * K)) := by
      simp [Stilde_axis P hd, stildeDLogRate, K]
    _ = P.q / (2 * P.p) *
        (Real.rpow K (-1 / P.p) / K) := by
      field_simp [P.p_pos.ne', hK.ne']
    _ = P.q / (2 * P.p) *
        Real.rpow K (-1 - 1 / P.p) := by rw [hpow]
    _ = P.q / (2 * P.p) *
        Real.rpow (-(P.q * d) / 2) (-1 - 1 / P.p) := by
      rfl

/-! ## `scalarDataAt` on the axis -/

theorem scalarDataAt_axis_S (P : Params) {d : ℝ} (hd : d < 0) :
    (scalarDataAt P 0 d).S =
      Real.rpow (-(P.q * d) / 2) (-1 / P.p) := by
  exact Stilde_axis P hd

@[simp] theorem scalarDataAt_axis_dSdt (P : Params) (d : ℝ) :
    (scalarDataAt P 0 d).dSdt = 0 := by
  exact deriv_Stilde_t_axis P d

theorem scalarDataAt_axis_dSdd (P : Params) {d : ℝ} (hd : d < 0) :
    (scalarDataAt P 0 d).dSdd =
      P.q / (2 * P.p) *
        Real.rpow (-(P.q * d) / 2) (-1 - 1 / P.p) := by
  exact deriv_Stilde_d_axis P hd

/-- All three fields of `scalarDataAt` in one exact identity. -/
theorem scalarDataAt_axis (P : Params) {d : ℝ} (hd : d < 0) :
    scalarDataAt P 0 d =
      { S := Real.rpow (-(P.q * d) / 2) (-1 / P.p)
        dSdt := 0
        dSdd := P.q / (2 * P.p) *
          Real.rpow (-(P.q * d) / 2) (-1 - 1 / P.p) } := by
  simp [scalarDataAt, Stilde_axis P hd, deriv_Stilde_t_axis,
    deriv_Stilde_d_axis P hd]

/-! ## Jet and coefficient specializations -/

/-- On the axis, `Γ₀ = 2 ∂ₓγ + 4γ²`. -/
@[simp] theorem gamma0_zero (z : Jet) :
    gamma0 0 z = 2 * z.dx + 4 * z.val ^ 2 := by
  simp [gamma0]

/-- The scalar data composed with an axis jet. -/
theorem scalarDataOfJet_axis (P : Params) (z : Jet)
    (hgamma : gamma0 0 z < 0) :
    scalarDataOfJet P 0 z =
      { S := Real.rpow (-(P.q * gamma0 0 z) / 2) (-1 / P.p)
        dSdt := 0
        dSdd := P.q / (2 * P.p) *
          Real.rpow (-(P.q * gamma0 0 z) / 2) (-1 - 1 / P.p) } := by
  exact scalarDataAt_axis P hgamma

/-- The noncharacteristic coefficient on the axis. -/
theorem coeff0_scalarDataAt_axis
    (P : Params) (z : Jet) {d : ℝ} (hd : d < 0) :
    coeff0 0 z (scalarDataAt P 0 d) =
      P.q / P.p *
        Real.rpow (-(P.q * d) / 2) (-1 - 1 / P.p) := by
  rw [coeff0_zero, scalarDataAt_axis_dSdd P hd]
  ring

@[simp] theorem coeff1_scalarDataAt_axis (P : Params) (z : Jet) (d : ℝ) :
    coeff1 0 z (scalarDataAt P 0 d) = 0 :=
  coeff1_zero z (scalarDataAt P 0 d)

@[simp] theorem coeff2_scalarDataAt_axis (P : Params) (z : Jet) (d : ℝ) :
    coeff2 0 z (scalarDataAt P 0 d) = 0 :=
  coeff2_zero z (scalarDataAt P 0 d)

/-- The exact lower-order term on the axis, before composing `d = Γ₀`. -/
theorem lowerOrder_scalarDataAt_axis
    (P : Params) (z : Jet) {d : ℝ} (hd : d < 0) :
    lowerOrder P 0 z (scalarDataAt P 0 d) =
      (4 * P.q * z.val * z.dx / P.p) *
          Real.rpow (-(P.q * d) / 2) (-1 - 1 / P.p) +
        2 * z.val * (1 - 2 / P.p) *
          Real.rpow (-(P.q * d) / 2) (-1 / P.p) := by
  rw [lowerOrder_zero, scalarDataAt_axis_dSdd P hd,
    scalarDataAt_axis_S P hd]
  ring

/-- Manuscript formula for `c₀` after composing with `Γ₀`. -/
theorem coeff0_scalarDataOfJet_axis
    (P : Params) (z : Jet) (hgamma : gamma0 0 z < 0) :
    coeff0 0 z (scalarDataOfJet P 0 z) =
      P.q / P.p *
        Real.rpow (-(P.q * gamma0 0 z) / 2) (-1 - 1 / P.p) := by
  exact coeff0_scalarDataAt_axis P z hgamma

@[simp] theorem coeff1_scalarDataOfJet_axis (P : Params) (z : Jet) :
    coeff1 0 z (scalarDataOfJet P 0 z) = 0 :=
  coeff1_zero z (scalarDataOfJet P 0 z)

@[simp] theorem coeff2_scalarDataOfJet_axis (P : Params) (z : Jet) :
    coeff2 0 z (scalarDataOfJet P 0 z) = 0 :=
  coeff2_zero z (scalarDataOfJet P 0 z)

/-- Manuscript formula for `L₀` after composing with `Γ₀`. -/
theorem lowerOrder_scalarDataOfJet_axis
    (P : Params) (z : Jet) (hgamma : gamma0 0 z < 0) :
    lowerOrder P 0 z (scalarDataOfJet P 0 z) =
      (4 * P.q * z.val * z.dx / P.p) *
          Real.rpow (-(P.q * gamma0 0 z) / 2) (-1 - 1 / P.p) +
        2 * z.val * (1 - 2 / P.p) *
          Real.rpow (-(P.q * gamma0 0 z) / 2) (-1 / P.p) := by
  exact lowerOrder_scalarDataAt_axis P z hgamma

end

end StressTensor
