import StressTensor.CKAnalyticUniqueness
import StressTensor.CKFirstOrderAnalyticData
import StressTensor.FirstOrderFieldBridge
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.Tactic.FinCases

/-!
# Analytic uniqueness for the reduced two-component field

This file specializes analytic identity/uniqueness to the actual
two-component field used by the first-order reduction.  The central input is
equality of the complete scalar Frechet jet of each component at the origin.
For a two-variable analytic function this is precisely equality of all mixed
Taylor data, expressed without choosing coordinates.

The last part records the reconstruction uniqueness needed by
`CKOutcome.localUnique`: equality of the reduced `v` fields determines the
original scalar field once their values agree on the Cauchy axis.  Thus the
only equation-specific uniqueness obligation left to the CK recursion is
equality of the two component jets at the origin.
-/

namespace StressTensor

noncomputable section

open Set Filter

/-! ## The centered analytic box -/

/-- The centered open rectangle on which the local CK construction lives. -/
def centeredAnalyticBox (rx ry : ℝ) : Set Point :=
  Ioo (-rx) rx ×ˢ Ioo (-ry) ry

@[simp] theorem mem_centeredAnalyticBox {rx ry : ℝ} {p : Point} :
    p ∈ centeredAnalyticBox rx ry ↔
      |p.1| < rx ∧ |p.2| < ry := by
  simp [centeredAnalyticBox, abs_lt]

theorem isOpen_centeredAnalyticBox (rx ry : ℝ) :
    IsOpen (centeredAnalyticBox rx ry) :=
  isOpen_Ioo.prod isOpen_Ioo

theorem isPreconnected_centeredAnalyticBox (rx ry : ℝ) :
    IsPreconnected (centeredAnalyticBox rx ry) :=
  isPreconnected_Ioo.prod isPreconnected_Ioo

@[simp] theorem origin_mem_centeredAnalyticBox {rx ry : ℝ}
    (hrx : 0 < rx) (hry : 0 < ry) :
    (0, 0) ∈ centeredAnalyticBox rx ry := by
  simp [centeredAnalyticBox, hrx, hry]

/-! ## Full component jets -/

/-- Equality of the complete Frechet jets of both scalar components.

Since the domain is `Point = ℝ × ℝ`, these continuous multilinear maps
simultaneously encode every mixed `x`/`y` derivative of the given order. -/
def FirstOrderComponentJetsAgreeAt
    (U V : Point → FirstOrderState) (p : Point) : Prop :=
  ∀ (i : Fin 2) (n : ℕ),
    iteratedFDeriv ℝ n (fun z => U z i) p =
      iteratedFDeriv ℝ n (fun z => V z i) p

/-- The two coordinate directions of `Point`. -/
def pointCoordinateDirection : Fin 2 → Point
  | 0 => (1, 0)
  | 1 => (0, 1)

@[simp] theorem pointCoordinateDirection_zero :
    pointCoordinateDirection 0 = (1, 0) := rfl

@[simp] theorem pointCoordinateDirection_one :
    pointCoordinateDirection 1 = (0, 1) := rfl

/-- The two coordinate directions span the `(x,y)` plane. -/
theorem span_range_pointCoordinateDirection :
    Submodule.span ℝ (Set.range pointCoordinateDirection) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro p
  have hex : pointCoordinateDirection 0 ∈
      Submodule.span ℝ (Set.range pointCoordinateDirection) :=
    Submodule.subset_span (Set.mem_range_self 0)
  have hey : pointCoordinateDirection 1 ∈
      Submodule.span ℝ (Set.range pointCoordinateDirection) :=
    Submodule.subset_span (Set.mem_range_self 1)
  have h := Submodule.add_mem _
    (Submodule.smul_mem _ p.1 hex) (Submodule.smul_mem _ p.2 hey)
  simpa [pointCoordinateDirection] using h

/-- Two scalar multilinear maps on `Point` are equal if they agree on every
ordered tuple of coordinate directions. -/
theorem continuousMultilinearMap_eq_of_pointCoordinate_eq {n : ℕ}
    {A B : Point [×n]→L[ℝ] ℝ}
    (h : ∀ d : Fin n → Fin 2,
      A (fun j => pointCoordinateDirection (d j)) =
        B (fun j => pointCoordinateDirection (d j))) :
    A = B := by
  apply ContinuousMultilinearMap.ext
  have hml : A.toMultilinearMap = B.toMultilinearMap :=
    MultilinearMap.ext_of_span_eq_top
      (fun _ => span_range_pointCoordinateDirection) h
  intro v
  exact DFunLike.congr_fun hml v

/-- Equality of every coordinate mixed derivative of both scalar components.
The function `d` records, for every derivative slot, whether the derivative
is taken in the `x` or `y` direction. -/
def FirstOrderCoordinateJetsAgreeAt
    (U V : Point → FirstOrderState) (p : Point) : Prop :=
  ∀ (i : Fin 2) (n : ℕ) (d : Fin n → Fin 2),
    iteratedFDeriv ℝ n (fun z => U z i) p
        (fun j => pointCoordinateDirection (d j)) =
      iteratedFDeriv ℝ n (fun z => V z i) p
        (fun j => pointCoordinateDirection (d j))

/-- Coordinate mixed-derivative agreement is equivalent to the full-jet
input needed by analytic uniqueness. -/
theorem firstOrderComponentJetsAgreeAt_of_coordinateJets
    {U V : Point → FirstOrderState} {p : Point}
    (h : FirstOrderCoordinateJetsAgreeAt U V p) :
    FirstOrderComponentJetsAgreeAt U V p := by
  intro i n
  apply continuousMultilinearMap_eq_of_pointCoordinate_eq
  exact h i n

theorem firstOrderCoordinateJetsAgreeAt_of_componentJets
    {U V : Point → FirstOrderState} {p : Point}
    (h : FirstOrderComponentJetsAgreeAt U V p) :
    FirstOrderCoordinateJetsAgreeAt U V p := by
  intro i n d
  rw [h i n]

theorem firstOrderCoordinateJetsAgreeAt_iff_componentJets
    {U V : Point → FirstOrderState} {p : Point} :
    FirstOrderCoordinateJetsAgreeAt U V p ↔
      FirstOrderComponentJetsAgreeAt U V p :=
  ⟨firstOrderComponentJetsAgreeAt_of_coordinateJets,
    firstOrderCoordinateJetsAgreeAt_of_componentJets⟩

/-- Equality of full vector-valued Frechet jets implies equality throughout a
connected centered box. -/
theorem firstOrderField_eqOn_centeredAnalyticBox_of_iteratedFDeriv_eq
    {U V : Point → FirstOrderState} {rx ry : ℝ}
    (hU : AnalyticOnNhd ℝ U (centeredAnalyticBox rx ry))
    (hV : AnalyticOnNhd ℝ V (centeredAnalyticBox rx ry))
    (hrx : 0 < rx) (hry : 0 < ry)
    (hjet : ∀ n : ℕ,
      iteratedFDeriv ℝ n U (0, 0) = iteratedFDeriv ℝ n V (0, 0)) :
    Set.EqOn U V (centeredAnalyticBox rx ry) :=
  AnalyticOnNhd.eqOn_of_iteratedFDeriv_eq hU hV
    (isPreconnected_centeredAnalyticBox rx ry)
    (origin_mem_centeredAnalyticBox hrx hry) hjet

/-- Componentwise full jets suffice for uniqueness of a `Fin 2` field.  This
form is convenient for a coefficient recursion, which is naturally proved
one scalar component at a time. -/
theorem firstOrderField_eqOn_centeredAnalyticBox_of_componentJets
    {U V : Point → FirstOrderState} {rx ry : ℝ}
    (hU : AnalyticOnNhd ℝ U (centeredAnalyticBox rx ry))
    (hV : AnalyticOnNhd ℝ V (centeredAnalyticBox rx ry))
    (hrx : 0 < rx) (hry : 0 < ry)
    (hjet : FirstOrderComponentJetsAgreeAt U V (0, 0)) :
    Set.EqOn U V (centeredAnalyticBox rx ry) := by
  have hUc := analyticOnNhd_pi_iff.mp hU
  have hVc := analyticOnNhd_pi_iff.mp hV
  intro p hp
  funext i
  exact AnalyticOnNhd.eqOn_of_iteratedFDeriv_eq (hUc i) (hVc i)
    (isPreconnected_centeredAnalyticBox rx ry)
    (origin_mem_centeredAnalyticBox hrx hry) (hjet i) hp

/-- Explicit mixed-coordinate version of two-component analytic uniqueness. -/
theorem firstOrderField_eqOn_centeredAnalyticBox_of_coordinateJets
    {U V : Point → FirstOrderState} {rx ry : ℝ}
    (hU : AnalyticOnNhd ℝ U (centeredAnalyticBox rx ry))
    (hV : AnalyticOnNhd ℝ V (centeredAnalyticBox rx ry))
    (hrx : 0 < rx) (hry : 0 < ry)
    (hjet : FirstOrderCoordinateJetsAgreeAt U V (0, 0)) :
    Set.EqOn U V (centeredAnalyticBox rx ry) :=
  firstOrderField_eqOn_centeredAnalyticBox_of_componentJets
    hU hV hrx hry
    (firstOrderComponentJetsAgreeAt_of_coordinateJets hjet)

/-- Scalar analytic uniqueness on the same centered box.  Its conclusion has
exactly the shape required by `CKOutcome.localUnique`. -/
theorem scalarField_eqOn_centeredAnalyticBox_of_iteratedFDeriv_eq
    {gamma eta : ℝ → ℝ → ℝ} {rx ry : ℝ}
    (hgamma : AnalyticOnNhd ℝ (uncurried gamma)
      (centeredAnalyticBox rx ry))
    (heta : AnalyticOnNhd ℝ (uncurried eta)
      (centeredAnalyticBox rx ry))
    (hrx : 0 < rx) (hry : 0 < ry)
    (hjet : ∀ n : ℕ,
      iteratedFDeriv ℝ n (uncurried gamma) (0, 0) =
        iteratedFDeriv ℝ n (uncurried eta) (0, 0)) :
    Set.EqOn (uncurried gamma) (uncurried eta)
      (centeredAnalyticBox rx ry) :=
  AnalyticOnNhd.eqOn_of_iteratedFDeriv_eq hgamma heta
    (isPreconnected_centeredAnalyticBox rx ry)
    (origin_mem_centeredAnalyticBox hrx hry) hjet

/-! ## The actual reduced field associated with `gamma` -/

/-- The actual two-component reduced field `(v,r)` associated with a scalar
field `gamma`, presented as a function on `Point`. -/
def actualFirstOrderState (gamma : ℝ → ℝ → ℝ) :
    Point → FirstOrderState :=
  fun p => ![firstOrderVField gamma p.1 p.2,
    firstOrderRField gamma p.1 p.2]

@[simp] theorem actualFirstOrderState_zero
    (gamma : ℝ → ℝ → ℝ) (p : Point) :
    actualFirstOrderState gamma p 0 = firstOrderVField gamma p.1 p.2 := by
  rfl

@[simp] theorem actualFirstOrderState_one
    (gamma : ℝ → ℝ → ℝ) (p : Point) :
    actualFirstOrderState gamma p 1 = firstOrderRField gamma p.1 p.2 := by
  rfl

/-- Analyticity of a scalar field makes its actual first reduced component
analytic. -/
theorem analyticAt_actualFirstOrderVField
    {gamma : ℝ → ℝ → ℝ} {p : Point}
    (hgamma : AnalyticAt ℝ (uncurried gamma) p) :
    AnalyticAt ℝ
      (fun z : Point => firstOrderVField gamma z.1 z.2) p := by
  let f : Point → ℝ := uncurried gamma
  let vx : Point := (1, 0)
  have hfd : AnalyticAt ℝ (fderiv ℝ f) p := by
    simpa only [f] using hgamma.fderiv
  have hFx : AnalyticAt ℝ (fun z => fderiv ℝ f z vx) p :=
    (hfd.contDiffAt.clm_apply contDiffAt_const).analyticAt
  have hev : ∀ᶠ z in nhds p, AnalyticAt ℝ f z := by
    simpa only [f] using hgamma.eventually_analyticAt
  have heq :
      (fun z : Point => partialX gamma z.1 z.2) =ᶠ[nhds p]
        (fun z => fderiv ℝ f z vx) := by
    filter_upwards [hev] with z hz
    simpa only [f, vx] using
      partialX_eq_fderiv_uncurried hz.differentiableAt
  have hpartial : AnalyticAt ℝ
      (fun z : Point => partialX gamma z.1 z.2) p :=
    hFx.congr heq.symm
  have hone : AnalyticAt ℝ (fun _ : Point => (1 : ℝ)) p :=
    analyticAt_const
  have hraw := hpartial.add hone
  apply hraw.congr
  exact Filter.Eventually.of_forall fun _ => rfl

/-- Analyticity of a scalar field makes its actual second reduced component
analytic. -/
theorem analyticAt_actualFirstOrderRField
    {gamma : ℝ → ℝ → ℝ} {p : Point}
    (hgamma : AnalyticAt ℝ (uncurried gamma) p) :
    AnalyticAt ℝ
      (fun z : Point => firstOrderRField gamma z.1 z.2) p := by
  let f : Point → ℝ := uncurried gamma
  let vy : Point := (0, 1)
  have hfd : AnalyticAt ℝ (fderiv ℝ f) p := by
    simpa only [f] using hgamma.fderiv
  have hFy : AnalyticAt ℝ (fun z => fderiv ℝ f z vy) p :=
    (hfd.contDiffAt.clm_apply contDiffAt_const).analyticAt
  have hev : ∀ᶠ z in nhds p, AnalyticAt ℝ f z := by
    simpa only [f] using hgamma.eventually_analyticAt
  have heq :
      (fun z : Point => partialY gamma z.1 z.2) =ᶠ[nhds p]
        (fun z => fderiv ℝ f z vy) := by
    filter_upwards [hev] with z hz
    simpa only [f, vy] using
      partialY_eq_fderiv_uncurried hz.differentiableAt
  have hpartial : AnalyticAt ℝ
      (fun z : Point => partialY gamma z.1 z.2) p :=
    hFy.congr heq.symm
  have hy : AnalyticAt ℝ (fun z : Point => z.2) p := analyticAt_snd
  have hdiv : AnalyticAt ℝ
      (fun z : Point => z.2 * partialY gamma z.1 z.2 / 2) p :=
    (hy.mul hpartial).div_const
  have hraw := hgamma.add hdiv
  apply hraw.congr
  exact Filter.Eventually.of_forall fun z => by
    simp [uncurried, firstOrderRField, gamma2Field, gamma2, jetOf]

/-- The actual `Fin 2` reduced field is analytic wherever `gamma` is. -/
theorem analyticAt_actualFirstOrderState
    {gamma : ℝ → ℝ → ℝ} {p : Point}
    (hgamma : AnalyticAt ℝ (uncurried gamma) p) :
    AnalyticAt ℝ (actualFirstOrderState gamma) p := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · simpa using analyticAt_actualFirstOrderVField hgamma
  · simpa using analyticAt_actualFirstOrderRField hgamma

theorem analyticOnNhd_actualFirstOrderState
    {gamma : ℝ → ℝ → ℝ} {S : Set Point}
    (hgamma : AnalyticOnNhd ℝ (uncurried gamma) S) :
    AnalyticOnNhd ℝ (actualFirstOrderState gamma) S := by
  intro p hp
  exact analyticAt_actualFirstOrderState (hgamma p hp)

/-! ## Reconstruction uniqueness -/

/-- On a centered box, a scalar field is determined by its `x` derivative
and its values on the Cauchy axis. -/
theorem scalarField_eqOn_centeredAnalyticBox_of_partialX_eq_of_axis_eq
    {gamma eta : ℝ → ℝ → ℝ} {rx ry : ℝ}
    (hgamma : AnalyticOnNhd ℝ (uncurried gamma)
      (centeredAnalyticBox rx ry))
    (heta : AnalyticOnNhd ℝ (uncurried eta)
      (centeredAnalyticBox rx ry))
    (hrx : 0 < rx)
    (hpartial : ∀ x y, |x| < rx → |y| < ry →
      partialX gamma x y = partialX eta x y)
    (haxis : ∀ y, |y| < ry → gamma 0 y = eta 0 y) :
    Set.EqOn (uncurried gamma) (uncurried eta)
      (centeredAnalyticBox rx ry) := by
  intro p hp
  rcases (mem_centeredAnalyticBox.mp hp) with ⟨hpx, hpy⟩
  let s : Set ℝ := Ioo (-rx) rx
  have hzero : (0 : ℝ) ∈ s := by simp [s, hrx]
  have hpx' : p.1 ∈ s := by simpa [s, abs_lt] using hpx
  have hdiffGamma : DifferentiableOn ℝ (fun x => gamma x p.2) s := by
    intro x hx
    have hxabs : |x| < rx := by simpa [s, abs_lt] using hx
    have hpoint : (x, p.2) ∈ centeredAnalyticBox rx ry :=
      mem_centeredAnalyticBox.mpr ⟨hxabs, hpy⟩
    exact (gammaDifferentialDataAt_of_analyticAt
      (hgamma (x, p.2) hpoint)).dx.differentiableAt.differentiableWithinAt
  have hdiffEta : DifferentiableOn ℝ (fun x => eta x p.2) s := by
    intro x hx
    have hxabs : |x| < rx := by simpa [s, abs_lt] using hx
    have hpoint : (x, p.2) ∈ centeredAnalyticBox rx ry :=
      mem_centeredAnalyticBox.mpr ⟨hxabs, hpy⟩
    exact (gammaDifferentialDataAt_of_analyticAt
      (heta (x, p.2) hpoint)).dx.differentiableAt.differentiableWithinAt
  have hderiv : s.EqOn
      (deriv fun x => gamma x p.2) (deriv fun x => eta x p.2) := by
    intro x hx
    have hxabs : |x| < rx := by simpa [s, abs_lt] using hx
    exact hpartial x p.2 hxabs hpy
  have heq := (isOpen_Ioo : IsOpen s).eqOn_of_deriv_eq
    isPreconnected_Ioo hdiffGamma hdiffEta hderiv hzero (haxis p.2 hpy)
  exact heq hpx'

/-- Equality of the actual reduced fields determines the original scalar
fields when their Cauchy-axis values agree. -/
theorem scalarField_eqOn_of_actualFirstOrderState_eqOn
    {gamma eta : ℝ → ℝ → ℝ} {rx ry : ℝ}
    (hgamma : AnalyticOnNhd ℝ (uncurried gamma)
      (centeredAnalyticBox rx ry))
    (heta : AnalyticOnNhd ℝ (uncurried eta)
      (centeredAnalyticBox rx ry))
    (hrx : 0 < rx)
    (hstate : Set.EqOn (actualFirstOrderState gamma)
      (actualFirstOrderState eta) (centeredAnalyticBox rx ry))
    (haxis : ∀ y, |y| < ry → gamma 0 y = eta 0 y) :
    Set.EqOn (uncurried gamma) (uncurried eta)
      (centeredAnalyticBox rx ry) := by
  apply scalarField_eqOn_centeredAnalyticBox_of_partialX_eq_of_axis_eq
    hgamma heta hrx
  · intro x y hx hy
    have hmem : (x, y) ∈ centeredAnalyticBox rx ry :=
      mem_centeredAnalyticBox.mpr ⟨hx, hy⟩
    have hpoint := hstate hmem
    have hcomponent := congrFun hpoint 0
    simpa [firstOrderVField] using hcomponent
  · exact haxis

/-! ## Cauchy rows of the actual reduced field -/

/-- The zero value Cauchy datum forces the tangential derivative on the
Cauchy axis to vanish.  This uses only that the datum holds on an open
interval; no additional regularity hypothesis is needed because `deriv` is
local. -/
theorem partialY_zero_on_cauchyAxis_of_hasCauchyDataOn
    {gamma : ℝ → ℝ → ℝ} {radius y : ℝ}
    (hdata : HasCauchyDataOn gamma radius) (hy : |y| < radius) :
    partialY gamma 0 y = 0 := by
  have hyIoo : y ∈ Ioo (-radius) radius := by
    simpa [abs_lt] using hy
  have heq : (gamma 0) =ᶠ[nhds y] (fun _ : ℝ => 0) := by
    filter_upwards [(isOpen_Ioo.mem_nhds hyIoo)] with z hz
    exact (hdata (by simpa [abs_lt] using hz)).1
  unfold partialY
  rw [heq.deriv_eq]
  simp

/-- Both actual reduced components have zero Cauchy row. -/
theorem actualFirstOrderState_zero_on_cauchyAxis_of_hasCauchyDataOn
    {gamma : ℝ → ℝ → ℝ} {radius y : ℝ}
    (hdata : HasCauchyDataOn gamma radius) (hy : |y| < radius) :
    actualFirstOrderState gamma (0, y) = 0 := by
  funext i
  fin_cases i
  · have hx := (hdata hy).2
    simp [actualFirstOrderState, firstOrderVField, hx]
  · have hvalue := (hdata hy).1
    have hdy := partialY_zero_on_cauchyAxis_of_hasCauchyDataOn hdata hy
    simp [actualFirstOrderState, firstOrderRField, gamma2Field, gamma2,
      jetOf, hvalue, hdy]

/-- In particular, the actual reduced state of a CK solution has the zero
row on every part of the Cauchy axis covered by its data radius. -/
theorem actualFirstOrderState_zero_on_cauchyAxis_of_ckSolution
    {P : Params} {gamma : ℝ → ℝ → ℝ} {S : Set Point}
    {radius y : ℝ} (hgamma : IsCKSolution P S radius gamma)
    (hy : |y| < radius) :
    actualFirstOrderState gamma (0, y) = 0 :=
  actualFirstOrderState_zero_on_cauchyAxis_of_hasCauchyDataOn
    hgamma.2.2 hy

/-- Two analytic CK solutions on the centered box agree once their actual
reduced fields agree.  Their common zero Cauchy value supplies the axis
hypothesis automatically. -/
theorem ckSolutions_eqOn_of_actualFirstOrderState_eqOn
    {P : Params} {gamma eta : ℝ → ℝ → ℝ}
    {rx ry radius : ℝ}
    (hgamma : IsCKSolution P (centeredAnalyticBox rx ry) radius gamma)
    (heta : IsCKSolution P (centeredAnalyticBox rx ry) radius eta)
    (hrx : 0 < rx) (hryRadius : ry ≤ radius)
    (hstate : Set.EqOn (actualFirstOrderState gamma)
      (actualFirstOrderState eta) (centeredAnalyticBox rx ry)) :
    Set.EqOn (uncurried gamma) (uncurried eta)
      (centeredAnalyticBox rx ry) := by
  apply scalarField_eqOn_of_actualFirstOrderState_eqOn
    hgamma.1 heta.1 hrx hstate
  intro y hy
  have hyradius : |y| < radius := lt_of_lt_of_le hy hryRadius
  exact (hgamma.2.2 hyradius).1.trans (heta.2.2 hyradius).1.symm

/-- Production uniqueness theorem: equation-specific equality of the two
component jets at the origin propagates through analytic uniqueness and
reconstruction to equality of the original CK solutions. -/
theorem ckSolutions_eqOn_of_actualFirstOrderComponentJets
    {P : Params} {gamma eta : ℝ → ℝ → ℝ}
    {rx ry radius : ℝ}
    (hgamma : IsCKSolution P (centeredAnalyticBox rx ry) radius gamma)
    (heta : IsCKSolution P (centeredAnalyticBox rx ry) radius eta)
    (hrx : 0 < rx) (hry : 0 < ry) (hryRadius : ry ≤ radius)
    (hjet : FirstOrderComponentJetsAgreeAt
      (actualFirstOrderState gamma) (actualFirstOrderState eta) (0, 0)) :
    Set.EqOn (uncurried gamma) (uncurried eta)
      (centeredAnalyticBox rx ry) := by
  have hstate := firstOrderField_eqOn_centeredAnalyticBox_of_componentJets
    (analyticOnNhd_actualFirstOrderState hgamma.1)
    (analyticOnNhd_actualFirstOrderState heta.1) hrx hry hjet
  exact ckSolutions_eqOn_of_actualFirstOrderState_eqOn
    hgamma heta hrx hryRadius hstate

/-- Coordinate mixed-derivative form of the production CK uniqueness
theorem. -/
theorem ckSolutions_eqOn_of_actualFirstOrderCoordinateJets
    {P : Params} {gamma eta : ℝ → ℝ → ℝ}
    {rx ry radius : ℝ}
    (hgamma : IsCKSolution P (centeredAnalyticBox rx ry) radius gamma)
    (heta : IsCKSolution P (centeredAnalyticBox rx ry) radius eta)
    (hrx : 0 < rx) (hry : 0 < ry) (hryRadius : ry ≤ radius)
    (hjet : FirstOrderCoordinateJetsAgreeAt
      (actualFirstOrderState gamma) (actualFirstOrderState eta) (0, 0)) :
    Set.EqOn (uncurried gamma) (uncurried eta)
      (centeredAnalyticBox rx ry) :=
  ckSolutions_eqOn_of_actualFirstOrderComponentJets hgamma heta hrx hry
    hryRadius (firstOrderComponentJetsAgreeAt_of_coordinateJets hjet)

/-- A jet-determinacy theorem for every competing CK solution is precisely
a provider for the `locallyUnique` field of `CKOutcome`. -/
theorem ckLocalUniqueOn_centeredAnalyticBox_of_componentJet_determinacy
    {P : Params} {gamma : ℝ → ℝ → ℝ}
    {rx ry radius : ℝ}
    (hgamma : IsCKSolution P (centeredAnalyticBox rx ry) radius gamma)
    (hrx : 0 < rx) (hry : 0 < ry) (hryRadius : ry ≤ radius)
    (hdet : ∀ eta : ℝ → ℝ → ℝ,
      IsCKSolution P (centeredAnalyticBox rx ry) radius eta →
      FirstOrderComponentJetsAgreeAt
        (actualFirstOrderState eta) (actualFirstOrderState gamma) (0, 0)) :
    ∀ eta : ℝ → ℝ → ℝ,
      IsCKSolution P (centeredAnalyticBox rx ry) radius eta →
      Set.EqOn (uncurried eta) (uncurried gamma)
        (centeredAnalyticBox rx ry) := by
  intro eta heta
  exact ckSolutions_eqOn_of_actualFirstOrderComponentJets
    heta hgamma hrx hry hryRadius (hdet eta heta)

/-- A coordinate mixed-jet determinacy theorem also directly provides the
`CKOutcome.localUnique` conclusion. -/
theorem ckLocalUniqueOn_centeredAnalyticBox_of_coordinateJet_determinacy
    {P : Params} {gamma : ℝ → ℝ → ℝ}
    {rx ry radius : ℝ}
    (hgamma : IsCKSolution P (centeredAnalyticBox rx ry) radius gamma)
    (hrx : 0 < rx) (hry : 0 < ry) (hryRadius : ry ≤ radius)
    (hdet : ∀ eta : ℝ → ℝ → ℝ,
      IsCKSolution P (centeredAnalyticBox rx ry) radius eta →
      FirstOrderCoordinateJetsAgreeAt
        (actualFirstOrderState eta) (actualFirstOrderState gamma) (0, 0)) :
    ∀ eta : ℝ → ℝ → ℝ,
      IsCKSolution P (centeredAnalyticBox rx ry) radius eta →
      Set.EqOn (uncurried eta) (uncurried gamma)
        (centeredAnalyticBox rx ry) := by
  intro eta heta
  exact ckSolutions_eqOn_of_actualFirstOrderCoordinateJets
    heta hgamma hrx hry hryRadius (hdet eta heta)

end

end StressTensor
