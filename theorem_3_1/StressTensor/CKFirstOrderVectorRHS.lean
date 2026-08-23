import StressTensor.CKFirstOrderAnalyticData
import Mathlib.Tactic.FinCases

/-!
# Vector form of the reduced first-order right-hand side

The convergence and evaluation layers use a two-component vector equation.
This file records that its matrix-vector expression is exactly the pair of
scalar rates appearing in the first-order reconstruction layer.
-/

namespace StressTensor

noncomputable section

/-- The matrix principal term plus the derivative-free source is exactly
the pair `(firstOrderVRate, firstOrderRRate)`. -/
theorem firstOrder_vector_rhs_eq
    (P : Params) (w : FirstOrderPhase) (d : FirstOrderState) :
    Matrix.mulVec (firstOrderPrincipalArray P w) ((w 0) • d) +
        firstOrderSourceVector P w =
      ![firstOrderVRate P w (d 0) (d 1), firstOrderRRate w (d 0)] := by
  funext i
  fin_cases i <;>
    simp [firstOrderPrincipalArray, firstOrderPrincipalCore,
      firstOrderSourceVector, firstOrderVRate, firstOrderRRate,
      firstOrderSourceRate, Matrix.mulVec, dotProduct] <;> ring

/-- The Fréchet derivative in the first coordinate agrees componentwise
with the corresponding curried scalar derivatives. -/
theorem fderiv_apply_xDirection_eq
    {U : (ℝ × ℝ) → FirstOrderState} {x y : ℝ}
    (hU : DifferentiableAt ℝ U (x, y)) :
    fderiv ℝ U (x, y) (1, 0) =
      fun i => deriv (fun xi => U (xi, y) i) x := by
  funext i
  have hslice := hU.hasFDerivAt.comp_hasDerivAt x
    (hasFDerivAt_prodMk_left x y).hasDerivAt
  have hi := (ContinuousLinearMap.proj (R := ℝ) i).hasFDerivAt.comp_hasDerivAt
    x hslice
  exact hi.deriv.symm

/-- The analogous identity in the second coordinate. -/
theorem fderiv_apply_yDirection_eq
    {U : (ℝ × ℝ) → FirstOrderState} {x y : ℝ}
    (hU : DifferentiableAt ℝ U (x, y)) :
    fderiv ℝ U (x, y) (0, 1) =
      fun i => deriv (fun eta => U (x, eta) i) y := by
  funext i
  have hslice := hU.hasFDerivAt.comp_hasDerivAt y
    (hasFDerivAt_prodMk_right x y).hasDerivAt
  have hi := (ContinuousLinearMap.proj (R := ℝ) i).hasFDerivAt.comp_hasDerivAt
    y hslice
  exact hi.deriv.symm

end
end StressTensor
