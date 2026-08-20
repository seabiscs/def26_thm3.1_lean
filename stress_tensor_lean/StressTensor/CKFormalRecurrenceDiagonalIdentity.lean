import StressTensor.CKFormalDiagonalCongruence

/-!
# From the ordinary recurrence to the homogeneous formal identity

The reduced coefficient recurrence is written in integrated form,

`a (m+1,n) = (m+1)⁻¹ reducedArrayRHS(m,n)`.

This file packages the ordinary coefficients of `∂x U`, removes that
integration factor exactly, and then uses polar canonicalization to identify
the resulting canonical bivariate formal series with the reduced formal
right-hand side on every homogeneous diagonal.
-/

namespace StressTensor
namespace CKFormalRecurrenceDiagonalIdentity

open CKFirstOrderFormalSystem CKFirstOrderConvergence
  CKFormalDiagonalCongruence CKPolarUniqueness

noncomputable section

/-- Vector-valued ordinary coefficients of the formal `x` derivative. -/
def xDerivativeCoefficientArray
    (a : BivariateStateCoeff) : BivariateStateCoeff :=
  fun m n => ((m + 1 : ℕ) : ℝ) • a (m + 1) n

@[simp] theorem xDerivativeCoefficientArray_apply
    (a : BivariateStateCoeff) (m n : ℕ) :
    xDerivativeCoefficientArray a m n =
      ((m + 1 : ℕ) : ℝ) • a (m + 1) n :=
  rfl

/-- The integrated reduced recurrence is exactly the non-integrated
coefficient identity for `∂x U`. -/
theorem xDerivativeCoefficientArray_apply_eq_reducedArrayRHS
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (a : BivariateStateCoeff)
    (ha : SatisfiesReducedArrayRecurrence N b a)
    (m n : ℕ) :
    xDerivativeCoefficientArray a m n = reducedArrayRHS N b a m n := by
  rw [xDerivativeCoefficientArray_apply, ha m n]
  unfold reducedNextXCoefficient
  rw [smul_smul]
  have hm : (((m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [mul_inv_cancel₀ hm, one_smul]

/-- Array-valued form of the exact derivative recurrence. -/
theorem xDerivativeCoefficientArray_eq_reducedArrayRHS
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (a : BivariateStateCoeff)
    (ha : SatisfiesReducedArrayRecurrence N b a) :
    xDerivativeCoefficientArray a = reducedArrayRHS N b a := by
  funext m n
  exact xDerivativeCoefficientArray_apply_eq_reducedArrayRHS
    N b a ha m n

/-- The reduced array right-hand side is definitionally the polar
coefficient array of the reduced formal right-hand side. -/
theorem reducedArrayRHS_eq_polarCoefficientArray
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (a : BivariateStateCoeff) :
    reducedArrayRHS N b a =
      polarCoefficientArray (reducedRHS N b (stateBivariateFMS a)) := by
  rfl

/-- Homogeneous diagonal form of the reduced equation.  It says that the
canonical FMS of the ordinary `x`-derivative coefficients and the formal
right-hand side have identical degree-`k` diagonal evaluations. -/
theorem stateBivariateFMS_xDerivativeCoefficientArray_apply_diag
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (a : BivariateStateCoeff)
    (ha : SatisfiesReducedArrayRecurrence N b a)
    (k : ℕ) (x y : ℝ) :
    stateBivariateFMS (xDerivativeCoefficientArray a) k
        (fun _ : Fin k => (x, y)) =
      reducedRHS N b (stateBivariateFMS a) k
        (fun _ : Fin k => (x, y)) := by
  rw [xDerivativeCoefficientArray_eq_reducedArrayRHS N b a ha,
    reducedArrayRHS_eq_polarCoefficientArray]
  exact stateBivariateFMS_polarCoefficientArray_apply_diag
    (reducedRHS N b (stateBivariateFMS a)) k x y

/-- Relation-valued packaging of the full homogeneous diagonal identity. -/
theorem stateBivariateFMS_xDerivativeCoefficientArray_diagonallyEquivalent
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (a : BivariateStateCoeff)
    (ha : SatisfiesReducedArrayRecurrence N b a) :
    DiagonallyEquivalent
      (stateBivariateFMS (xDerivativeCoefficientArray a))
      (reducedRHS N b (stateBivariateFMS a)) := by
  intro k z
  exact stateBivariateFMS_xDerivativeCoefficientArray_apply_diag
    N b a ha k z.1 z.2

/-! ## Compatibility with the scalar coefficient derivative -/

/-- Each scalar component of the vector derivative array is the existing
ordinary coefficient derivative `CKSeriesBridge.coeffX`. -/
theorem componentCoeff_xDerivativeCoefficientArray
    (a : BivariateStateCoeff) (i : Fin 2) :
    CKVectorAnalyticEvaluation.componentCoeff
        (xDerivativeCoefficientArray a) i =
      CKSeriesBridge.coeffX
        (CKVectorAnalyticEvaluation.componentCoeff a i) := by
  funext m n
  simp [CKVectorAnalyticEvaluation.componentCoeff,
    xDerivativeCoefficientArray, CKSeriesBridge.coeffX]

/-- Family-valued version of the component compatibility theorem. -/
theorem stateComponents_xDerivativeCoefficientArray
    (a : BivariateStateCoeff) :
    CKVectorAnalyticEvaluation.stateComponents
        (xDerivativeCoefficientArray a) =
      fun i => CKSeriesBridge.coeffX
        (CKVectorAnalyticEvaluation.componentCoeff a i) := by
  funext i
  exact componentCoeff_xDerivativeCoefficientArray a i

end


end CKFormalRecurrenceDiagonalIdentity
end StressTensor
