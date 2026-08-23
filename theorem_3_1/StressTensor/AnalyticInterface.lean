import Mathlib.Analysis.Analytic.Basic
import StressTensor.Ansatz
import StressTensor.AuxiliaryEquation
import StressTensor.Bounds
import StressTensor.Symmetry

/-!
# Analytic and Cauchy--Kowalevskaya interface

Mathlib currently has no ready-to-apply Cauchy--Kowalevskaya theorem in the
generality used by the reference.  This file therefore does two things:

* it connects the finite-dimensional jet formulas to actual iterated `deriv`s;
* it packages the precise existence/uniqueness conclusion needed from CK as
  data, without adding an axiom or using a proof placeholder.

Consequences such as normal form, evenness from uniqueness, and strict
spacelikeness after localization are then ordinary proved theorems.
-/

namespace StressTensor

noncomputable section

/-- A point in the `(x,y)` plane. -/
abbrev Point := ℝ × ℝ

/-- Regard a curried two-variable function as a function on `ℝ × ℝ`. -/
def uncurried (γ : ℝ → ℝ → ℝ) : Point → ℝ :=
  fun z => γ z.1 z.2

/-- First partial derivative in `x`, represented by Mathlib's total `deriv`. -/
def partialX (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun ξ => γ ξ y) x

/-- First partial derivative in `y`. -/
def partialY (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (γ x) y

/-- Second partial derivative `∂ₓₓγ`. -/
def partialXX (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun ξ => partialX γ ξ y) x

/-- Mixed partial derivative, with `x` differentiated first and then `y`. -/
def partialXY (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun η => partialX γ x η) y

/-- Second partial derivative `∂ᵧᵧγ`. -/
def partialYY (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun η => partialY γ x η) y

/-- The five-component jet used on the right-hand side of (3.23). -/
def jetOf (γ : ℝ → ℝ → ℝ) (x y : ℝ) : Jet where
  val := γ x y
  dx := partialX γ x y
  dy := partialY γ x y
  dxy := partialXY γ x y
  dyy := partialYY γ x y

/-- `S̃` together with its two partial derivatives at `(t,d)`. -/
def scalarDataAt (P : Params) (t d : ℝ) : ScalarData where
  S := Stilde P t d
  dSdt := deriv (fun τ => Stilde P τ d) t
  dSdd := deriv (Stilde P t) d

/-- The scalar data composed with `(y, Γ₀)` as in (3.8). -/
def scalarDataOfJet (P : Params) (y : ℝ) (z : Jet) : ScalarData :=
  scalarDataAt P y (gamma0 y z)

/-- The analytic auxiliary equation (3.22), interpreted using actual derivatives. -/
def auxiliaryEquationAt (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) : Prop :=
  let z := jetOf γ x y
  residualNormal P y z (partialXX γ x y) (scalarDataOfJet P y z) = 0

/-- A function solves the auxiliary equation at every point of `U`. -/
def SolvesAuxiliaryOn
    (P : Params) (U : Set Point) (γ : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃x y : ℝ⦄, (x, y) ∈ U → auxiliaryEquationAt P γ x y

/-- The two analytic Cauchy data in (3.24). -/
def HasCauchyDataOn (γ : ℝ → ℝ → ℝ) (r : ℝ) : Prop :=
  ∀ ⦃y : ℝ⦄, |y| < r → γ 0 y = 0 ∧ partialX γ 0 y = -1

/-- All properties required of a local solution for the CK uniqueness argument. -/
def IsCKSolution
    (P : Params) (U : Set Point) (r : ℝ) (γ : ℝ → ℝ → ℝ) : Prop :=
  AnalyticOnNhd ℝ (uncurried γ) U ∧
    SolvesAuxiliaryOn P U γ ∧ HasCauchyDataOn γ r

/-- Reflection in the transverse variable. -/
def reflectFunction (γ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun x y => γ x (-y)

/--
The exact output needed from Cauchy--Kowalevskaya: a local analytic solution
and uniqueness among analytic solutions with the same equation and data.
This is a structure, not an axiom; clients must construct it from a CK theorem.
-/
structure CKOutcome (P : Params) (U : Set Point) (r : ℝ) where
  isOpen_domain : IsOpen U
  origin_mem : (0, 0) ∈ U
  radius_pos : 0 < r
  cauchy_axis_mem : ∀ ⦃y : ℝ⦄, |y| < r → (0, y) ∈ U
  gamma : ℝ → ℝ → ℝ
  solution : IsCKSolution P U r gamma
  locallyUnique :
    ∀ η : ℝ → ℝ → ℝ, IsCKSolution P U r η →
      Set.EqOn (uncurried η) (uncurried gamma) U

/-- CK uniqueness makes the solution even once reflection invariance is supplied. -/
theorem CKOutcome.even_of_reflection_solution
    {P : Params} {U : Set Point} {r : ℝ} (K : CKOutcome P U r)
    (hreflect : IsCKSolution P U r (reflectFunction K.gamma))
    ⦃x y : ℝ⦄ (hxy : (x, y) ∈ U) :
    K.gamma x (-y) = K.gamma x y := by
  exact K.locallyUnique (reflectFunction K.gamma) hreflect hxy

/-- The coefficient form is equivalent to CK normal form wherever `c₀ ≠ 0`. -/
theorem auxiliaryEquation_iff_normalForm
    (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ)
    (hcoeff0 :
      coeff0 y (jetOf γ x y) (scalarDataOfJet P y (jetOf γ x y)) ≠ 0) :
    auxiliaryEquationAt P γ x y ↔
      partialXX γ x y = normalForm P y (jetOf γ x y)
        (scalarDataOfJet P y (jetOf γ x y)) := by
  simpa [auxiliaryEquationAt] using
    residualNormal_eq_zero_iff P y (jetOf γ x y) (partialXX γ x y)
      (scalarDataOfJet P y (jetOf γ x y)) hcoeff0

/-- The modular scalar estimates of (3.19)--(3.20) make `c₀` positive on `U_q`. -/
theorem coeff0_pos_of_inU
    (P : Params) {x y : ℝ} {z : Jet} (a : ScalarData)
    (hU : InU P x y z)
    (hS : (1 : ℝ) / 8 ≤ a.S)
    (hderiv : a.S * ((P.q - 1) / 32) ≤ a.dSdd) :
    0 < coeff0 y z a := by
  have hqsub : 0 < P.q - 1 := sub_pos.mpr P.one_lt_q
  have hq : 0 < (P.q - 1) / 1024 := div_pos hqsub (by norm_num)
  exact lt_of_lt_of_le hq
    (coeff0_ge_q_sub_one_div_1024_of_inU P a hU hS hderiv)

/-- Localization to `U_q` places `Γ₀` strictly below `-1`. -/
theorem gamma0_lt_neg_one_of_inU
    {P : Params} {x y : ℝ} {z : Jet} (hU : InU P x y z) :
    gamma0 y z < -1 := by
  have hneg := (inV_gamma0_of_inU hU).neg_d_bounds
  linarith

/-- On the light line the ansatz gradient is exactly `(1,0)`. -/
@[simp] theorem ansatzGradient_zero (z : Jet) :
    ansatzGradient 0 z = (1, 0) := by
  simp [ansatzGradient]

/-- Off the light line, localization to `U_q` makes the gradient strictly spacelike. -/
theorem normSq_ansatz_lt_one_of_inU
    {P : Params} {x y : ℝ} {z : Jet} (hU : InU P x y z) (hy : y ≠ 0) :
    normSq (ansatzGradient y z) < 1 := by
  rw [normSq_ansatz]
  have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  have hgamma := gamma0_lt_neg_one_of_inU hU
  nlinarith

/-- The jet of the prescribed Cauchy data `(0,-1,0,0,0)`. -/
def initialJet : Jet where
  val := 0
  dx := -1
  dy := 0
  dxy := 0
  dyy := 0

@[simp] theorem gamma0_initial_origin : gamma0 0 initialJet = -2 := by
  norm_num [gamma0, gamma2, initialJet]

/-- The Cauchy jet belongs to `U_q` along the permitted initial segment. -/
theorem initialJet_inU (P : Params) {y : ℝ} (hy : |y| < P.rho) :
    InU P 0 y initialJet := by
  refine ⟨⟨?_, hy⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using P.rho_pos
  · simpa [initialJet] using P.rho_pos
  · simpa [initialJet] using P.rho_pos
  · simpa [initialJet] using P.rho_pos
  · norm_num [initialJet]
  · norm_num [initialJet]

end

end StressTensor
