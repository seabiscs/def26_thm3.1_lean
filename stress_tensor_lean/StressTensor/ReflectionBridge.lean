import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Shift
import StressTensor.AnalyticInterface
import StressTensor.Symmetry

/-!
# Reflection bridge for actual functions

This file lifts the finite-dimensional identities in `StressTensor.Symmetry`
to the `deriv`-based jets and Cauchy--Kowalevskaya interface.  No regularity
hypothesis is needed for the derivative identities: Mathlib's total `deriv`
commutes with precomposition by negation, including at nondifferentiable
points.
-/

namespace StressTensor

noncomputable section

/-! ## Derivatives of the reflected function -/

@[simp] theorem reflectFunction_apply
    (γ : ℝ → ℝ → ℝ) (x y : ℝ) : reflectFunction γ x y = γ x (-y) := rfl

@[simp] theorem reflectFunction_involutive (γ : ℝ → ℝ → ℝ) :
    reflectFunction (reflectFunction γ) = γ := by
  funext x y
  simp

@[simp] theorem partialX_reflectFunction
    (γ : ℝ → ℝ → ℝ) (x y : ℝ) :
    partialX (reflectFunction γ) x y = partialX γ x (-y) := by
  rfl

@[simp] theorem partialY_reflectFunction
    (γ : ℝ → ℝ → ℝ) (x y : ℝ) :
    partialY (reflectFunction γ) x y = -partialY γ x (-y) := by
  change deriv (fun η => γ x (-η)) y = -deriv (γ x) (-y)
  exact deriv_comp_neg (γ x) y

@[simp] theorem partialXX_reflectFunction
    (γ : ℝ → ℝ → ℝ) (x y : ℝ) :
    partialXX (reflectFunction γ) x y = partialXX γ x (-y) := by
  simp [partialXX]

@[simp] theorem partialXY_reflectFunction
    (γ : ℝ → ℝ → ℝ) (x y : ℝ) :
    partialXY (reflectFunction γ) x y = -partialXY γ x (-y) := by
  simp only [partialXY, partialX_reflectFunction]
  exact deriv_comp_neg (fun η => partialX γ x η) y

@[simp] theorem partialYY_reflectFunction
    (γ : ℝ → ℝ → ℝ) (x y : ℝ) :
    partialYY (reflectFunction γ) x y = partialYY γ x (-y) := by
  simp only [partialYY, partialY_reflectFunction]
  rw [show (fun η => -partialY γ x (-η)) =
      -(fun η => partialY γ x (-η)) by rfl]
  rw [deriv.neg, deriv_comp_neg]
  simp

@[simp] theorem jetOf_reflectFunction
    (γ : ℝ → ℝ → ℝ) (x y : ℝ) :
    jetOf (reflectFunction γ) x y = reflectJet (jetOf γ x (-y)) := by
  simp [jetOf, reflectJet]

/-! ## Evenness of the scalar factor and its derivative data -/

/-- The first partial derivative of the even scalar factor is odd. -/
@[simp] theorem deriv_Stilde_first_neg (P : Params) (t d : ℝ) :
    deriv (fun τ => Stilde P τ d) (-t) =
      -deriv (fun τ => Stilde P τ d) t := by
  have h := deriv_comp_neg (fun τ => Stilde P τ d) (-t)
  have heven : (fun τ => Stilde P (-τ) d) = (fun τ => Stilde P τ d) := by
    funext τ
    exact Stilde_neg P τ d
  rw [heven] at h
  simpa only [neg_neg] using h

/-- Differentiation in `d` preserves evenness in the first variable. -/
@[simp] theorem deriv_Stilde_second_neg (P : Params) (t d : ℝ) :
    deriv (Stilde P (-t)) d = deriv (Stilde P t) d := by
  have heven : Stilde P (-t) = Stilde P t := by
    funext δ
    exact Stilde_neg P t δ
  rw [heven]

@[simp] theorem scalarDataAt_neg (P : Params) (t d : ℝ) :
    scalarDataAt P (-t) d = reflectScalar (scalarDataAt P t d) := by
  simp [scalarDataAt, reflectScalar, Stilde_neg, deriv_Stilde_first_neg,
    deriv_Stilde_second_neg]

@[simp] theorem scalarDataOfJet_reflect
    (P : Params) (y : ℝ) (z : Jet) :
    scalarDataOfJet P (-y) (reflectJet z) =
      reflectScalar (scalarDataOfJet P y z) := by
  simp [scalarDataOfJet]

@[simp] theorem scalarDataOfJet_reflect_at_neg
    (P : Params) (y : ℝ) (z : Jet) :
    scalarDataOfJet P y (reflectJet z) =
      reflectScalar (scalarDataOfJet P (-y) z) := by
  simpa only [neg_neg] using scalarDataOfJet_reflect P (-y) z

/-! ## Equivariance of the actual auxiliary equation -/

@[simp] theorem auxiliaryEquationAt_reflectFunction
    (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) :
    auxiliaryEquationAt P (reflectFunction γ) x y ↔
      auxiliaryEquationAt P γ x (-y) := by
  simp only [auxiliaryEquationAt, jetOf_reflectFunction,
    partialXX_reflectFunction, scalarDataOfJet_reflect_at_neg]
  let z := jetOf γ x (-y)
  let dxx := partialXX γ x (-y)
  let a := scalarDataOfJet P (-y) z
  have hres :
      residualNormal P y (reflectJet z) dxx (reflectScalar a) =
        residualNormal P (-y) z dxx a := by
    simpa only [neg_neg] using residualNormal_reflect P (-y) z dxx a
  constructor
  · intro h
    rwa [hres] at h
  · intro h
    rwa [hres]

/-! ## Symmetric domains and preservation of the CK predicates -/

/-- Reflection of a point in the transverse coordinate. -/
def reflectPoint (p : Point) : Point := (p.1, -p.2)

@[simp] theorem reflectPoint_apply (x y : ℝ) :
    reflectPoint (x, y) = (x, -y) := rfl

@[simp] theorem reflectPoint_involutive (p : Point) :
    reflectPoint (reflectPoint p) = p := by
  rcases p with ⟨x, y⟩
  simp [reflectPoint]

/-- A domain is invariant under `y ↦ -y`. -/
def YSymmetric (U : Set Point) : Prop :=
  ∀ ⦃x y : ℝ⦄, (x, y) ∈ U ↔ (x, -y) ∈ U

theorem YSymmetric.reflected_mem
    {U : Set Point} (hU : YSymmetric U) {x y : ℝ} (hxy : (x, y) ∈ U) :
    (x, -y) ∈ U :=
  hU.mp hxy

theorem YSymmetric.mapsTo_reflectPoint
    {U : Set Point} (hU : YSymmetric U) : Set.MapsTo reflectPoint U U := by
  rintro ⟨x, y⟩ hxy
  exact hU.reflected_mem hxy

theorem solvesAuxiliaryOn_reflectFunction
    (P : Params) {U : Set Point} (hU : YSymmetric U)
    {γ : ℝ → ℝ → ℝ} (hγ : SolvesAuxiliaryOn P U γ) :
    SolvesAuxiliaryOn P U (reflectFunction γ) := by
  intro x y hxy
  rw [auxiliaryEquationAt_reflectFunction]
  exact hγ (hU.reflected_mem hxy)

theorem hasCauchyDataOn_reflectFunction
    {γ : ℝ → ℝ → ℝ} {r : ℝ} (hγ : HasCauchyDataOn γ r) :
    HasCauchyDataOn (reflectFunction γ) r := by
  intro y hy
  have hreflected : |-y| < r := by simpa using hy
  simpa only [reflectFunction_apply, partialX_reflectFunction] using
    hγ hreflected

/-- The uncurried reflected function is precomposition by point reflection. -/
theorem uncurried_reflectFunction (γ : ℝ → ℝ → ℝ) :
    uncurried (reflectFunction γ) = uncurried γ ∘ reflectPoint := by
  funext p
  rfl

theorem analyticAt_reflectPoint (p : Point) :
    AnalyticAt ℝ reflectPoint p := by
  change AnalyticAt ℝ (fun p : Point => (p.1, -p.2)) p
  exact analyticAt_fst.prod analyticAt_snd.neg

theorem analyticOnNhd_reflectPoint (U : Set Point) :
    AnalyticOnNhd ℝ reflectPoint U :=
  fun p _ => analyticAt_reflectPoint p

theorem analyticOnNhd_uncurried_reflectFunction
    {U : Set Point} (hU : YSymmetric U) {γ : ℝ → ℝ → ℝ}
    (hγ : AnalyticOnNhd ℝ (uncurried γ) U) :
    AnalyticOnNhd ℝ (uncurried (reflectFunction γ)) U := by
  have hcomp := hγ.comp (analyticOnNhd_reflectPoint U)
    hU.mapsTo_reflectPoint
  simpa only [uncurried_reflectFunction] using hcomp

theorem isCKSolution_reflectFunction
    (P : Params) {U : Set Point} {r : ℝ} (hU : YSymmetric U)
    {γ : ℝ → ℝ → ℝ} (hγ : IsCKSolution P U r γ) :
    IsCKSolution P U r (reflectFunction γ) := by
  exact ⟨analyticOnNhd_uncurried_reflectFunction hU hγ.1,
    solvesAuxiliaryOn_reflectFunction P hU hγ.2.1,
    hasCauchyDataOn_reflectFunction hγ.2.2⟩

/-- CK uniqueness forces evenness on every `y`-symmetric outcome domain. -/
theorem CKOutcome.even_of_ySymmetric
    {P : Params} {U : Set Point} {r : ℝ} (K : CKOutcome P U r)
    (hU : YSymmetric U) ⦃x y : ℝ⦄ (hxy : (x, y) ∈ U) :
    K.gamma x (-y) = K.gamma x y := by
  exact K.even_of_reflection_solution
    (isCKSolution_reflectFunction P hU K.solution) hxy

end

end StressTensor
