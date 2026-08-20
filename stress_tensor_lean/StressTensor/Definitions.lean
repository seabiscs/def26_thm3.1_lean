import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

/-!
# The stress-tensor ansatz: shared definitions

This file fixes the finite-dimensional data used in Sections 3.1--3.2 of the
reference.  The five fields of `Jet` correspond, in order, to
`(γ, ∂ₓγ, ∂ᵧγ, ∂ₓᵧγ, ∂ᵧᵧγ)`.  The missing derivative `∂ₓₓγ` is kept separate
because the auxiliary equation is solved for it.
-/

namespace StressTensor

noncomputable section

/-- Hölder-conjugate exponents in the range used by the construction. -/
structure Params where
  p : ℝ
  q : ℝ
  one_lt_q : 1 < q
  q_lt_two : q < 2
  two_lt_p : 2 < p
  holder : 1 / p + 1 / q = 1

namespace Params

/-- The radius `ϱ_q = 2⁻¹⁰ (q - 1) q⁻¹` from (3.17). -/
noncomputable def rho (P : Params) : ℝ :=
  (P.q - 1) / ((2 : ℝ) ^ 10 * P.q)

theorem q_pos (P : Params) : 0 < P.q := lt_trans (by norm_num) P.one_lt_q

theorem p_pos (P : Params) : 0 < P.p := lt_trans (by norm_num) P.two_lt_p

end Params

/-- The five derivatives which occur on the right-hand side of the CK normal form. -/
structure Jet where
  val : ℝ
  dx : ℝ
  dy : ℝ
  dxy : ℝ
  dyy : ℝ

/-- `Γ₁ = 1 + y² ∂ₓγ`, equation (3.3). -/
def gamma1 (y : ℝ) (z : Jet) : ℝ :=
  1 + y ^ 2 * z.dx

/-- `Γ₂ = γ + (y/2) ∂ᵧγ`, equation (3.3). -/
def gamma2 (y : ℝ) (z : Jet) : ℝ :=
  z.val + y * z.dy / 2

/-- `Γ₀ = 2∂ₓγ + y²(∂ₓγ)² + 4Γ₂²`, equation (3.5). -/
def gamma0 (y : ℝ) (z : Jet) : ℝ :=
  2 * z.dx + y ^ 2 * z.dx ^ 2 + 4 * gamma2 y z ^ 2

/-- The gradient predicted by the ansatz, expressed using its first jet. -/
def ansatzGradient (y : ℝ) (z : Jet) : ℝ × ℝ :=
  (gamma1 y z, 2 * y * gamma2 y z)

/-- Squared Euclidean norm on pairs. -/
def normSq (v : ℝ × ℝ) : ℝ :=
  v.1 ^ 2 + v.2 ^ 2

/-- The ansatz `u(x,y) = x + y² γ(x,y)`, equation (3.1). -/
def ansatz (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  x + y ^ 2 * γ x y

/--
The analytic continuation of the divided difference `C̃`, equation (3.6),
presented in the paper's piecewise form.  Its analyticity at `t = 0` is
proved in `ScalarAnalyticity` through an integral representation.
-/
noncomputable def Ctilde (P : Params) (t d : ℝ) : ℝ :=
  if t = 0 then -(P.q * d) / 2
  else (1 - Real.rpow (1 + t ^ 2 * d) (P.q / 2)) / t ^ 2

/-- `S̃`, equation (3.7), using `Real.rpow` for arbitrary real exponents. -/
noncomputable def Stilde (P : Params) (t d : ℝ) : ℝ :=
  Real.rpow (1 + t ^ 2 * d) ((P.q - 2) / 2) /
    Real.rpow (Ctilde P t d) (1 / P.p)

/-- `C(x,y) = C̃(y, Γ₀(x,y))`, equation (3.8), at the level of a jet. -/
noncomputable def Ccomp (P : Params) (y : ℝ) (z : Jet) : ℝ :=
  Ctilde P y (gamma0 y z)

/-- `S(x,y) = S̃(y, Γ₀(x,y))`, equation (3.8), at the level of a jet. -/
noncomputable def Scomp (P : Params) (y : ℝ) (z : Jet) : ℝ :=
  Stilde P y (gamma0 y z)

/-- Values of `S̃` and its two first partial derivatives at `(y, Γ₀)`. -/
structure ScalarData where
  S : ℝ
  dSdt : ℝ
  dSdd : ℝ

/-- The coefficient `c₀` in (3.16). -/
def coeff0 (y : ℝ) (z : Jet) (a : ScalarData) : ℝ :=
  y ^ 2 * a.S + 2 * gamma1 y z ^ 2 * a.dSdd

/-- The coefficient `c₁` in (3.16). -/
def coeff1 (y : ℝ) (z : Jet) (a : ScalarData) : ℝ :=
  4 * y * gamma1 y z * gamma2 y z * a.dSdd

/-- The coefficient `c₂` in (3.16). -/
def coeff2 (y : ℝ) (z : Jet) (a : ScalarData) : ℝ :=
  y ^ 2 * (a.S + 8 * gamma2 y z ^ 2 * a.dSdd)

/-- The lower-order term `L₀` in (3.16). -/
def lowerOrder (P : Params) (y : ℝ) (z : Jet) (a : ScalarData) : ℝ :=
  (3 * y * a.S + 24 * y * gamma2 y z ^ 2 * a.dSdd) * z.dy
    + 4 * y ^ 2 * gamma2 y z * a.dSdd * z.dx ^ 2
    + 8 * gamma1 y z * gamma2 y z * a.dSdd * z.dx
    + 2 * y * gamma2 y z * a.dSdt
    + 2 * (1 - 2 / P.p) * a.S * gamma2 y z

/-- The polynomial residual in (3.15), including the missing `∂ₓₓγ`. -/
def residualNormal
    (P : Params) (y : ℝ) (z : Jet) (dxx : ℝ) (a : ScalarData) : ℝ :=
  coeff0 y z a * dxx + 2 * coeff1 y z a * z.dxy
    + coeff2 y z a * z.dyy + lowerOrder P y z a

/-- The normal-form right-hand side `G`, equation (3.23). -/
def normalForm (P : Params) (y : ℝ) (z : Jet) (a : ScalarData) : ℝ :=
  -(2 * coeff1 y z a * z.dxy + coeff2 y z a * z.dyy
      + lowerOrder P y z a) / coeff0 y z a

/-- Membership in the square `Q_{ϱ_q}`. -/
def InQ (P : Params) (x y : ℝ) : Prop :=
  |x| < P.rho ∧ |y| < P.rho

/-- Membership in the jet domain `U_q`, equation (3.17). -/
def InU (P : Params) (x y : ℝ) (z : Jet) : Prop :=
  InQ P x y ∧ |z.val| < P.rho ∧ |z.dx + 1| < P.rho ∧
    |z.dy| < P.rho ∧ |z.dxy| < 1 ∧ |z.dyy| < 1

/-- Membership in the scalar domain `V_q`, equation (3.18). -/
def InV (P : Params) (t d : ℝ) : Prop :=
  |t| < P.rho ∧ |d + 2| < 4 * P.rho

end

end StressTensor
