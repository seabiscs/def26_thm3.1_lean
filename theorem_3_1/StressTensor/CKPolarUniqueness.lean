import StressTensor.CKFirstOrderFormalSystem
import StressTensor.CKFirstOrderAnalyticUniqueness
import StressTensor.CKPolarEvaluation
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Polar uniqueness for bivariate analytic series

A formal multilinear series need not use symmetric multilinear
representatives.  Consequently, equality of analytic functions does not in
general identify the representatives themselves.  It does identify their
symmetrizations, and in two variables those symmetrizations are exactly the
`polarCoefficient`s.

This file proves that diagonal vanishing of one homogeneous term forces all
of its polar coefficients to vanish.  It then packages the consequence for
two-component analytic germs and connects an arbitrary analytic germ to the
canonical bivariate FMS used by the reduced CK recurrence.
-/

namespace StressTensor
namespace CKPolarUniqueness

open Polynomial
open scoped BigOperators

noncomputable section

/-! ## Scalar coefficient extraction -/

/-- The scalar polynomial obtained by restricting a homogeneous term to
the affine line `(x,1)`.  Its coefficients are the polar coefficients of
that homogeneous term. -/
def scalarDiagonalPolynomial
    (p : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ) (k : ℕ) : ℝ[X] :=
  ∑ m ∈ Finset.range (k + 1),
    Polynomial.monomial m
      (CKPolarEvaluation.polarCoefficient p m (k - m))

/-- Evaluation of `scalarDiagonalPolynomial` is diagonal evaluation of the
corresponding homogeneous multilinear term. -/
theorem eval_scalarDiagonalPolynomial
    (p : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ)
    (k : ℕ) (x : ℝ) :
    Polynomial.eval x (scalarDiagonalPolynomial p k) =
      p k (fun _ : Fin k => (x, 1)) := by
  rw [scalarDiagonalPolynomial, Polynomial.eval_finsetSum,
    CKPolarEvaluation.apply_diag_eq_sum_polarCoefficient]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Polynomial.eval_monomial, one_pow, mul_one, smul_eq_mul]
  ring

/-- The coefficient of the diagonal polynomial at an admissible degree is
the corresponding polar coefficient. -/
theorem coeff_scalarDiagonalPolynomial
    (p : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ)
    {k m : ℕ} (hm : m ≤ k) :
    (scalarDiagonalPolynomial p k).coeff m =
      CKPolarEvaluation.polarCoefficient p m (k - m) := by
  rw [scalarDiagonalPolynomial, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single m]
  · simp
  · intro b hb hbm
    simp [hbm]
  · exact fun hmem => (hmem (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))).elim

/-- If the diagonal of a scalar homogeneous term vanishes identically,
then every polar coefficient of that degree vanishes. -/
theorem scalar_polarCoefficient_eq_zero_of_apply_diag_eq_zero
    (p : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ)
    (k : ℕ)
    (hdiag : ∀ x y : ℝ, p k (fun _ : Fin k => (x, y)) = 0)
    {m : ℕ} (hm : m ≤ k) :
    CKPolarEvaluation.polarCoefficient p m (k - m) = 0 := by
  have hpoly : scalarDiagonalPolynomial p k = 0 := by
    apply Polynomial.funext
    intro x
    rw [eval_scalarDiagonalPolynomial, hdiag]
    simp
  rw [← coeff_scalarDiagonalPolynomial p hm, hpoly]
  simp

/-- Total-degree form of scalar polar-coefficient uniqueness. -/
theorem scalar_polarCoefficient_eq_zero_of_apply_diag_eq_zero_total
    (p : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ)
    (hdiag : ∀ k : ℕ, ∀ z : ℝ × ℝ,
      p k (fun _ : Fin k => z) = 0)
    (m n : ℕ) :
    CKPolarEvaluation.polarCoefficient p m n = 0 := by
  have h := scalar_polarCoefficient_eq_zero_of_apply_diag_eq_zero
    p (m + n) (fun x y => hdiag (m + n) (x, y)) (Nat.le_add_right m n)
  simpa only [Nat.add_sub_cancel_left] using h

/-! ## Two-component lifting -/

/-- Extract one scalar component from a state-valued FMS. -/
def componentSeries
    (p : FormalMultilinearSeries ℝ (ℝ × ℝ) FirstOrderState)
    (a : Fin 2) : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ :=
  (ContinuousLinearMap.proj a).compFormalMultilinearSeries p

@[simp] theorem componentSeries_apply
    (p : FormalMultilinearSeries ℝ (ℝ × ℝ) FirstOrderState)
    (a : Fin 2) (k : ℕ) (z : Fin k → ℝ × ℝ) :
    componentSeries p a k z = p k z a := by
  rfl

theorem polarCoefficient_componentSeries
    (p : FormalMultilinearSeries ℝ (ℝ × ℝ) FirstOrderState)
    (a : Fin 2) (m n : ℕ) :
    CKPolarEvaluation.polarCoefficient (componentSeries p a) m n =
      CKPolarEvaluation.polarCoefficient p m n a := by
  unfold CKPolarEvaluation.polarCoefficient
  simp only [componentSeries_apply, Finset.sum_apply]

/-- If every diagonal value of a state-valued FMS vanishes, then every
two-component polar coefficient vanishes. -/
theorem state_polarCoefficient_eq_zero_of_apply_diag_eq_zero
    (p : FormalMultilinearSeries ℝ (ℝ × ℝ) FirstOrderState)
    (hdiag : ∀ k : ℕ, ∀ z : ℝ × ℝ,
      p k (fun _ : Fin k => z) = 0)
    (m n : ℕ) :
    CKPolarEvaluation.polarCoefficient p m n = 0 := by
  funext a
  rw [← polarCoefficient_componentSeries p a]
  apply scalar_polarCoefficient_eq_zero_of_apply_diag_eq_zero_total
  intro k z
  simp only [componentSeries_apply, hdiag, Pi.zero_apply]

/-! ## Consequences for analytic germs -/

theorem polarCoefficient_sub
    (p q : FormalMultilinearSeries ℝ (ℝ × ℝ) FirstOrderState)
    (m n : ℕ) :
    CKPolarEvaluation.polarCoefficient (p - q) m n =
      CKPolarEvaluation.polarCoefficient p m n -
        CKPolarEvaluation.polarCoefficient q m n := by
  unfold CKPolarEvaluation.polarCoefficient
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  rfl

/-- Mathlib's diagonal uniqueness theorem for analytic FMS germs, expressed
in the invariant bivariate coefficients appropriate to a possibly
nonsymmetric multilinear representative. -/
theorem HasFPowerSeriesAt.state_polarCoefficient_eq_zero
    {p : FormalMultilinearSeries ℝ (ℝ × ℝ) FirstOrderState}
    {x : ℝ × ℝ}
    (h : HasFPowerSeriesAt 0 p x) (m n : ℕ) :
    CKPolarEvaluation.polarCoefficient p m n = 0 := by
  apply state_polarCoefficient_eq_zero_of_apply_diag_eq_zero p
  intro k z
  exact h.apply_eq_zero k z

/-- Two FMS germs representing the same state-valued analytic function
have identical polar coefficients. -/
theorem HasFPowerSeriesAt.state_polarCoefficient_eq
    {f : (ℝ × ℝ) → FirstOrderState}
    {p q : FormalMultilinearSeries ℝ (ℝ × ℝ) FirstOrderState}
    {x : ℝ × ℝ}
    (hp : HasFPowerSeriesAt f p x)
    (hq : HasFPowerSeriesAt f q x) (m n : ℕ) :
    CKPolarEvaluation.polarCoefficient p m n =
      CKPolarEvaluation.polarCoefficient q m n := by
  have hz : HasFPowerSeriesAt 0 (p - q) x := by
    simpa only [sub_self] using hp.sub hq
  have hzero :=
    HasFPowerSeriesAt.state_polarCoefficient_eq_zero hz m n
  rw [polarCoefficient_sub, sub_eq_zero] at hzero
  exact hzero

/-- Equality of every diagonal homogeneous term makes two analytic germs
locally equal, even when their multilinear representatives differ away
from the diagonal. -/
theorem eventuallyEq_of_hasFPowerSeriesAt_of_apply_diag_eq
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F}
    {p q : FormalMultilinearSeries ℝ E F} {x : E}
    (hp : HasFPowerSeriesAt f p x)
    (hq : HasFPowerSeriesAt g q x)
    (hdiag : ∀ n : ℕ, ∀ z : E,
      p n (fun _ : Fin n => z) = q n (fun _ : Fin n => z)) :
    f =ᶠ[nhds x] g := by
  filter_upwards [hp.eventually_hasSum_sub,
    hq.eventually_hasSum_sub] with y hpy hqy
  have hqy' : HasSum
      (fun n : ℕ => p n (fun _ : Fin n => y - x)) (g y) := by
    apply hqy.congr_fun
    intro n
    exact hdiag n (y - x)
  exact hpy.unique hqy'

/-- Equality of diagonal homogeneous terms therefore identifies every
iterated Frechet derivative at the common center. -/
theorem iteratedFDeriv_eq_of_hasFPowerSeriesAt_of_apply_diag_eq
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F}
    {p q : FormalMultilinearSeries ℝ E F} {x : E}
    (hp : HasFPowerSeriesAt f p x)
    (hq : HasFPowerSeriesAt g q x)
    (hdiag : ∀ n : ℕ, ∀ z : E,
      p n (fun _ : Fin n => z) = q n (fun _ : Fin n => z))
    (n : ℕ) :
    iteratedFDeriv ℝ n f x = iteratedFDeriv ℝ n g x := by
  exact ((eventuallyEq_of_hasFPowerSeriesAt_of_apply_diag_eq
    hp hq hdiag).iteratedFDeriv ℝ n).self_of_nhds

/-! ## Canonicalization by polar coefficients -/

open CKFirstOrderFormalSystem

/-- The two definitions of polar coefficients used by the generic
evaluation layer and the formal reduced-system layer agree definitionally. -/
theorem formal_polarCoefficient_eq_evaluation_polarCoefficient
    (p : StateSeries) (m n : ℕ) :
    CKFirstOrderFormalSystem.polarCoefficient p m n =
      CKPolarEvaluation.polarCoefficient p m n := by
  rfl

/-- Polar coefficients of an arbitrary state-valued FMS, packaged as the
bivariate array consumed by the formal reduced recurrence. -/
def polarCoefficientArray (p : StateSeries) : BivariateStateCoeff :=
  fun m n => CKPolarEvaluation.polarCoefficient p m n

/-- Diagonal evaluation of the canonical bivariate state FMS. -/
theorem stateBivariateFMS_apply_diag
    (a : BivariateStateCoeff) (k : ℕ) (x y : ℝ) :
    stateBivariateFMS a k (fun _ : Fin k => (x, y)) =
      ∑ m ∈ Finset.range (k + 1),
        (x ^ m * y ^ (k - m)) • a m (k - m) := by
  funext i
  simp only [stateBivariateFMS, FormalMultilinearSeries.pi,
    ContinuousMultilinearMap.pi_apply,
    CKAnalyticEvaluation.bivariateFMS_apply_diag,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- Canonicalizing an FMS by its polar coefficients preserves every
diagonal homogeneous value. -/
theorem stateBivariateFMS_polarCoefficientArray_apply_diag
    (p : StateSeries) (k : ℕ) (x y : ℝ) :
    stateBivariateFMS (polarCoefficientArray p) k
        (fun _ : Fin k => (x, y)) =
      p k (fun _ : Fin k => (x, y)) := by
  rw [stateBivariateFMS_apply_diag,
    CKPolarEvaluation.apply_diag_eq_sum_polarCoefficient]
  rfl

/-- An analytic germ and the canonical FMS formed from its polar
coefficients have the same full vector-valued jet at the center. -/
theorem iteratedFDeriv_eq_canonical_polarSeries
    {U V : (ℝ × ℝ) → FirstOrderState}
    {p : StateSeries} {x : ℝ × ℝ}
    (hU : HasFPowerSeriesAt U p x)
    (hV : HasFPowerSeriesAt V
      (stateBivariateFMS (polarCoefficientArray p)) x)
    (n : ℕ) :
    iteratedFDeriv ℝ n U x = iteratedFDeriv ℝ n V x := by
  apply iteratedFDeriv_eq_of_hasFPowerSeriesAt_of_apply_diag_eq hU hV
  intro k z
  exact (stateBivariateFMS_polarCoefficientArray_apply_diag
    p k z.1 z.2).symm

/-- Componentwise full-jet form of canonical polar-series uniqueness. -/
theorem firstOrderComponentJetsAgreeAt_canonical_polarSeries
    {U V : (ℝ × ℝ) → FirstOrderState}
    {p : StateSeries} {x : ℝ × ℝ}
    (hU : HasFPowerSeriesAt U p x)
    (hV : HasFPowerSeriesAt V
      (stateBivariateFMS (polarCoefficientArray p)) x) :
    FirstOrderComponentJetsAgreeAt U V x := by
  have heq := eventuallyEq_of_hasFPowerSeriesAt_of_apply_diag_eq hU hV
    (fun k z => (stateBivariateFMS_polarCoefficientArray_apply_diag
      p k z.1 z.2).symm)
  intro i n
  exact (((heq.fun_comp fun u => u i).iteratedFDeriv ℝ n).self_of_nhds)

/-! ## Cauchy-row extraction -/

/-- Continuous-linear inclusion of the `y` axis. -/
def yAxisInclusion : ℝ →L[ℝ] ℝ × ℝ :=
  ContinuousLinearMap.inr ℝ ℝ ℝ

@[simp] theorem yAxisInclusion_apply (y : ℝ) :
    yAxisInclusion y = (0, y) := rfl

/-- The polar coefficient with zero `x` degree is evaluation with every
slot in the `y` direction. -/
theorem polarCoefficient_zero_left
    (p : StateSeries) (n : ℕ) :
    CKPolarEvaluation.polarCoefficient p 0 n =
      p n (fun _ : Fin n => (0, 1)) := by
  unfold CKPolarEvaluation.polarCoefficient CKPolarEvaluation.polarSlotInput
  simp
  rw [Nat.zero_add]

/-- Local vanishing on the `y` axis supplies the zero Cauchy row for the
polar coefficient array of an analytic germ. -/
theorem HasFPowerSeriesAt.hasReducedCauchyRow_polarCoefficientArray
    {U : (ℝ × ℝ) → FirstOrderState} {p : StateSeries}
    (hp : HasFPowerSeriesAt U p 0)
    (haxis : (fun y : ℝ => U (0, y)) =ᶠ[nhds 0] 0) :
    HasReducedCauchyRow (polarCoefficientArray p) 0 := by
  have hcomp : HasFPowerSeriesAt (U ∘ yAxisInclusion)
      (p.compContinuousLinearMap yAxisInclusion) 0 :=
    hp.compContinuousLinearMap
  have hzero : HasFPowerSeriesAt 0
      (p.compContinuousLinearMap yAxisInclusion) 0 := by
    apply hcomp.congr
    change (fun y : ℝ => U (0, y)) =ᶠ[nhds 0] 0
    exact haxis
  intro n
  rw [polarCoefficientArray, polarCoefficient_zero_left]
  have hz := hzero.apply_eq_zero n 1
  change p n (fun _ : Fin n => (0, 1)) = 0
  convert hz using 1
  funext i
  rfl

/-- Zero Cauchy data on a positive interval make the actual reduced field
locally zero along the `y` axis. -/
theorem eventuallyEq_zero_yAxis_actualFirstOrderState
    {gamma : ℝ → ℝ → ℝ} {radius : ℝ}
    (hdata : HasCauchyDataOn gamma radius) (hradius : 0 < radius) :
    (fun y : ℝ => actualFirstOrderState gamma (0, y)) =ᶠ[nhds 0] 0 := by
  have hzero : (0 : ℝ) ∈ Set.Ioo (-radius) radius := by
    simp [hradius]
  filter_upwards [isOpen_Ioo.mem_nhds hzero] with y hy
  apply actualFirstOrderState_zero_on_cauchyAxis_of_hasCauchyDataOn hdata
  apply abs_lt.mpr
  simpa only [Set.mem_Ioo] using hy

/-- The analytic germ of an actual reduced field with zero Cauchy data has
the zero formal Cauchy row. -/
theorem hasReducedCauchyRow_polarCoefficientArray_actualFirstOrderState
    {gamma : ℝ → ℝ → ℝ} {radius : ℝ} {p : StateSeries}
    (hp : HasFPowerSeriesAt (actualFirstOrderState gamma) p 0)
    (hdata : HasCauchyDataOn gamma radius) (hradius : 0 < radius) :
    HasReducedCauchyRow (polarCoefficientArray p) 0 :=
  HasFPowerSeriesAt.hasReducedCauchyRow_polarCoefficientArray hp
    (eventuallyEq_zero_yAxis_actualFirstOrderState hdata hradius)

/-! ## Formal-recurrence uniqueness to analytic-jet uniqueness -/

/-- Formal uniqueness identifies the polar coefficient array of any formal
competitor satisfying the same recurrence and Cauchy row. -/
theorem polarCoefficientArray_eq_formalReducedSolution
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (cauchy : ℕ → FirstOrderState) (p : StateSeries)
    (hp : IsFormalReducedSolution N b cauchy
      (polarCoefficientArray p)) :
    polarCoefficientArray p = formalReducedSolution N b cauchy :=
  IsFormalReducedSolution.unique N b cauchy hp
    (formalReducedSolution_isFormalSolution N b cauchy)

/-- Generic competitor bridge.  Once the analytic competitor's polar array
is proved to satisfy the formal recurrence, formal uniqueness and polar
canonicalization force equality of every component jet with the convergent
formal solution. -/
theorem firstOrderComponentJetsAgreeAt_formalReducedSolution
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (cauchy : ℕ → FirstOrderState)
    {U V : (ℝ × ℝ) → FirstOrderState} {p : StateSeries}
    (hU : HasFPowerSeriesAt U p 0)
    (hformal : IsFormalReducedSolution N b cauchy
      (polarCoefficientArray p))
    (hV : HasFPowerSeriesAt V
      (stateBivariateFMS (formalReducedSolution N b cauchy)) 0) :
    FirstOrderComponentJetsAgreeAt U V 0 := by
  have harr := polarCoefficientArray_eq_formalReducedSolution
    N b cauchy p hformal
  have hV' : HasFPowerSeriesAt V
      (stateBivariateFMS (polarCoefficientArray p)) 0 := by
    rw [harr]
    exact hV
  exact firstOrderComponentJetsAgreeAt_canonical_polarSeries hU hV'

/-- Analyticity-only wrapper around the generic competitor bridge.  The
remaining equation-specific obligation is stated as a provider converting
any FMS germ of the competitor into the formal recurrence. -/
theorem firstOrderComponentJetsAgreeAt_formalReducedSolution_of_analyticAt
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (cauchy : ℕ → FirstOrderState)
    {U V : (ℝ × ℝ) → FirstOrderState}
    (hU : AnalyticAt ℝ U 0)
    (hformal : ∀ p : StateSeries, HasFPowerSeriesAt U p 0 →
      IsFormalReducedSolution N b cauchy (polarCoefficientArray p))
    (hV : HasFPowerSeriesAt V
      (stateBivariateFMS (formalReducedSolution N b cauchy)) 0) :
    FirstOrderComponentJetsAgreeAt U V 0 := by
  rcases hU with ⟨p, hp⟩
  exact firstOrderComponentJetsAgreeAt_formalReducedSolution
    N b cauchy hp (hformal p hp) hV

/-- Zero-row version of the analytic competitor bridge.  Local vanishing
on the Cauchy axis supplies `HasReducedCauchyRow`; callers only need to
derive the coefficient recurrence from their PDE. -/
theorem firstOrderComponentJetsAgreeAt_formalReducedSolution_of_zeroAxis
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    {U V : (ℝ × ℝ) → FirstOrderState}
    (hU : AnalyticAt ℝ U 0)
    (haxis : (fun y : ℝ => U (0, y)) =ᶠ[nhds 0] 0)
    (hrecurrence : ∀ p : StateSeries, HasFPowerSeriesAt U p 0 →
      SatisfiesReducedArrayRecurrence N b (polarCoefficientArray p))
    (hV : HasFPowerSeriesAt V
      (stateBivariateFMS (formalReducedSolution N b 0)) 0) :
    FirstOrderComponentJetsAgreeAt U V 0 := by
  rcases hU with ⟨p, hp⟩
  have hrow : HasReducedCauchyRow (polarCoefficientArray p) 0 :=
    HasFPowerSeriesAt.hasReducedCauchyRow_polarCoefficientArray hp haxis
  exact firstOrderComponentJetsAgreeAt_formalReducedSolution
    N b 0 hp ⟨hrow, hrecurrence p hp⟩ hV

/-- Stress-tensor specialization of the zero-row competitor bridge.  The
formal target is the convergent canonical series selected in
`firstOrderFormalCoefficients`; the remaining recurrence provider is the
precise interface to the PDE-to-FMS evaluation layer. -/
theorem actualFirstOrderState_componentJetsAgree_firstOrderFormalCoefficients
    (P : Params)
    {gamma : ℝ → ℝ → ℝ} {radius : ℝ}
    {V : (ℝ × ℝ) → FirstOrderState}
    (hgamma : AnalyticAt ℝ (uncurried gamma) 0)
    (hdata : HasCauchyDataOn gamma radius) (hradius : 0 < radius)
    (hrecurrence : ∀ p : StateSeries,
      HasFPowerSeriesAt (actualFirstOrderState gamma) p 0 →
      SatisfiesReducedArrayRecurrence
        (firstOrderPrincipalOriginMajorant P).series
        (firstOrderSourceOriginMajorant P).series
        (polarCoefficientArray p))
    (hV : HasFPowerSeriesAt V
      (stateBivariateFMS (firstOrderFormalCoefficients P)) 0) :
    FirstOrderComponentJetsAgreeAt (actualFirstOrderState gamma) V 0 := by
  have hU : AnalyticAt ℝ (actualFirstOrderState gamma) 0 :=
    analyticAt_actualFirstOrderState hgamma
  have haxis := eventuallyEq_zero_yAxis_actualFirstOrderState
    hdata hradius
  apply firstOrderComponentJetsAgreeAt_formalReducedSolution_of_zeroAxis
    (firstOrderPrincipalOriginMajorant P).series
    (firstOrderSourceOriginMajorant P).series hU haxis hrecurrence
  simpa only [firstOrderFormalCoefficients] using hV

/-- Coordinate mixed-jet form of the stress-tensor competitor bridge. -/
theorem actualFirstOrderState_coordinateJetsAgree_firstOrderFormalCoefficients
    (P : Params)
    {gamma : ℝ → ℝ → ℝ} {radius : ℝ}
    {V : (ℝ × ℝ) → FirstOrderState}
    (hgamma : AnalyticAt ℝ (uncurried gamma) 0)
    (hdata : HasCauchyDataOn gamma radius) (hradius : 0 < radius)
    (hrecurrence : ∀ p : StateSeries,
      HasFPowerSeriesAt (actualFirstOrderState gamma) p 0 →
      SatisfiesReducedArrayRecurrence
        (firstOrderPrincipalOriginMajorant P).series
        (firstOrderSourceOriginMajorant P).series
        (polarCoefficientArray p))
    (hV : HasFPowerSeriesAt V
      (stateBivariateFMS (firstOrderFormalCoefficients P)) 0) :
    FirstOrderCoordinateJetsAgreeAt (actualFirstOrderState gamma) V 0 :=
  firstOrderCoordinateJetsAgreeAt_of_componentJets
    (actualFirstOrderState_componentJetsAgree_firstOrderFormalCoefficients
      P hgamma hdata hradius hrecurrence hV)

end

end CKPolarUniqueness
end StressTensor
