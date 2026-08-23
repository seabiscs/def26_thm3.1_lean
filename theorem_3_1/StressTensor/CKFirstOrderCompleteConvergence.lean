import StressTensor.CKSmallParameter
import StressTensor.CKNagumoTransportClosure
import StressTensor.CKStableTransportMajorant
import StressTensor.CKNormalizedResidualMajorant
import StressTensor.CKNormalizedResidualScaling

/-!
# Complete convergence bounds for the first-order formal system

This module closes the normalized Nagumo majorant argument.  It fixes explicit
smallness, tangential, and evolution rates, proves the nonlinear residual
transport estimate, and derives unconditional diagonal and componentwise
geometric bounds for the recursively defined formal coefficients.
-/

namespace StressTensor
namespace CKFirstOrderCompleteConvergence

open CKFirstOrderFormalSystem CKFirstOrderConvergence CKNagumoMajorant
  CKSmallParameter CKNagumoTransportClosure CKNormalizedResidualMajorant
  CKNormalizedResidualScaling

noncomputable section

def principalInverseRadius (P : Params) : ℝ :=
  ((firstOrderPrincipalOriginMajorant P).radius : ℝ)⁻¹

def sourceInverseRadius (P : Params) : ℝ :=
  ((firstOrderSourceOriginMajorant P).radius : ℝ)⁻¹

def epsilon (P : Params) : ℝ :=
  commonSmallEpsilon (principalInverseRadius P) (sourceInverseRadius P)

def tangentialRate (P : Params) : ℝ := CKSmallParameter.tangentialRate (epsilon P)

def principalSlope (P : Params) : ℝ :=
  CKNormalizedResidualMajorant.principalNagumoSlope
    (firstOrderPrincipalOriginMajorant P) (epsilon P)

def sourceSlope (P : Params) : ℝ :=
  CKNormalizedResidualMajorant.sourceNagumoSlope
    (firstOrderSourceOriginMajorant P) (epsilon P)

def linearSize (P : Params) : ℝ :=
  2 * ‖firstOrderPrincipalArray P firstOrderOrigin‖

def pointSourceSize (P : Params) : ℝ :=
  (firstOrderSourceOriginMajorant P).coefficientBound

def quadraticSize (P : Params) : ℝ := 32 * principalSlope P

def evolutionRate (P : Params) : ℝ :=
  CKNagumoTransportClosure.evolutionRate
    (linearSize P) (pointSourceSize P) (sourceSlope P)
      (quadraticSize P) (epsilon P)

def residualProfile (P : Params) (k : ℕ) : ℝ :=
  (if k = 0 then pointSourceSize P else 0) +
    sourceSlope P * epsilon P * nagumoCoeff k +
    quadraticSize P * epsilon P ^ 2 * (k + 1 : ℝ) * nagumoCoeff (k + 1)

theorem principalInverseRadius_nonneg (P : Params) :
    0 ≤ principalInverseRadius P := by
  exact inv_nonneg.mpr (firstOrderPrincipalOriginMajorant P).radius_real_pos.le

theorem sourceInverseRadius_nonneg (P : Params) :
    0 ≤ sourceInverseRadius P := by
  exact inv_nonneg.mpr (firstOrderSourceOriginMajorant P).radius_real_pos.le

theorem epsilon_pos (P : Params) : 0 < epsilon P := by
  exact commonSmallEpsilon_pos (principalInverseRadius_nonneg P)
    (sourceInverseRadius_nonneg P)

theorem epsilon_small_principal (P : Params) :
    8 * (epsilon P * ((firstOrderPrincipalOriginMajorant P).radius : ℝ)⁻¹) < 1 := by
  exact commonSmallEpsilon_first (principalInverseRadius_nonneg P)
    (sourceInverseRadius_nonneg P)

theorem epsilon_small_source (P : Params) :
    8 * (epsilon P * ((firstOrderSourceOriginMajorant P).radius : ℝ)⁻¹) < 1 := by
  exact commonSmallEpsilon_second (principalInverseRadius_nonneg P)
    (sourceInverseRadius_nonneg P)

theorem tangentialRate_pos (P : Params) : 0 < tangentialRate P := by
  exact CKSmallParameter.tangentialRate_pos (epsilon_pos P)

theorem tangentialRate_inverse_le (P : Params) :
    (tangentialRate P)⁻¹ ≤ epsilon P * nagumoCoeff 1 := by
  exact (CKSmallParameter.inv_tangentialRate_eq_nagumo (epsilon_pos P)).le

theorem principalSlope_nonneg (P : Params) : 0 ≤ principalSlope P := by
  exact CKNormalizedResidualMajorant.principalNagumoSlope_nonneg
    (firstOrderPrincipalOriginMajorant P) (epsilon_small_principal P)

theorem sourceSlope_nonneg (P : Params) : 0 ≤ sourceSlope P := by
  exact CKNormalizedResidualMajorant.sourceNagumoSlope_nonneg
    (firstOrderSourceOriginMajorant P) (epsilon_small_source P)

theorem linearSize_nonneg (P : Params) : 0 ≤ linearSize P := by
  unfold linearSize
  exact mul_nonneg (by norm_num) (norm_nonneg _)

theorem pointSourceSize_nonneg (P : Params) : 0 ≤ pointSourceSize P :=
  (firstOrderSourceOriginMajorant P).coefficientBound_pos.le

theorem quadraticSize_nonneg (P : Params) : 0 ≤ quadraticSize P := by
  unfold quadraticSize
  exact mul_nonneg (by norm_num) (principalSlope_nonneg P)

theorem evolutionRate_pos (P : Params) : 0 < evolutionRate P := by
  exact CKNagumoTransportClosure.evolutionRate_pos
    (linearSize_nonneg P) (pointSourceSize_nonneg P)
    (sourceSlope_nonneg P) (quadraticSize_nonneg P) (epsilon_pos P)

theorem residualProfile_nonneg (P : Params) (k : ℕ) :
    0 ≤ residualProfile P k := by
  have hzero : 0 ≤ if k = 0 then pointSourceSize P else 0 := by
    split
    · exact pointSourceSize_nonneg P
    · exact le_rfl
  have hsource : 0 ≤ sourceSlope P * epsilon P * nagumoCoeff k :=
    mul_nonneg (mul_nonneg (sourceSlope_nonneg P) (epsilon_pos P).le)
      (nagumoCoeff_nonneg k)
  have hquad : 0 ≤ quadraticSize P * epsilon P ^ 2 * (k + 1 : ℝ) *
      nagumoCoeff (k + 1) := by
    have hk : 0 ≤ (k : ℝ) + 1 := by positivity
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (quadraticSize_nonneg P) (sq_nonneg (epsilon P)))
        hk)
      (nagumoCoeff_nonneg _)
  exact add_nonneg (add_nonneg hzero hsource) hquad

theorem transport_step (P : Params) : ∀ k : ℕ,
    linearSize P * (k : ℝ) * (epsilon P * nagumoCoeff k) +
        residualProfile P k ≤
      ((k + 1 : ℕ) : ℝ) * evolutionRate P *
        (epsilon P * nagumoCoeff (k + 1)) := by
  apply CKNagumoTransportClosure.nagumo_transport_step
    (ε := epsilon P) (L := linearSize P) (B := pointSourceSize P)
    (C := sourceSlope P) (D := quadraticSize P)
    (R := evolutionRate P) (g := residualProfile P)
    (epsilon_pos P) (linearSize_nonneg P) (pointSourceSize_nonneg P)
    (sourceSlope_nonneg P) (quadraticSize_nonneg P)
  · exact CKNagumoTransportClosure.le_evolutionRate _ _ _ _ _
  · intro k
    simp only [residualProfile]
    push_cast
    exact le_rfl

theorem firstOrderFormalCoefficients_diagonalTransportBound_of_residual
    (P : Params)
    (hresidual : ∀ u : BivariateStateCoeff, u 0 0 = 0 →
      (∀ i j, ‖u i j‖ ≤
        CKFuchsianMajorant.diagonalTransportEnvelope
          (fun k => epsilon P * nagumoCoeff k)
          (evolutionRate P) (tangentialRate P) i j) →
      ∀ m n,
        ‖firstOrderNonlinearResidual P u m n‖ ≤
          ((m + n).choose m : ℝ) * evolutionRate P ^ m *
            tangentialRate P ^ n * residualProfile P (m + n)) :
    ∀ m n, ‖firstOrderFormalCoefficients P m n‖ ≤
      CKFuchsianMajorant.diagonalTransportEnvelope
        (fun k => epsilon P * nagumoCoeff k)
        (evolutionRate P) (tangentialRate P) m n := by
  apply CKStableTransportMajorant.norm_le_diagonalTransportEnvelope_of_causal_vector_recurrence_zeroOrigin
    (a := firstOrderFormalCoefficients P)
    (transport := firstOrderBaseTransport P (firstOrderFormalCoefficients P))
    (nonlinear := firstOrderNonlinearResidual P)
    (c := fun k => epsilon P * nagumoCoeff k)
    (g := residualProfile P)
    (L := linearSize P) (R := evolutionRate P) (S := tangentialRate P)
  · exact linearSize_nonneg P
  · exact (evolutionRate_pos P).le
  · exact (tangentialRate_pos P).le
  · intro k
    exact mul_nonneg (epsilon_pos P).le (nagumoCoeff_nonneg k)
  · exact transport_step P
  · intro n
    rw [firstOrderFormalCoefficients_zero_x, norm_zero]
    exact mul_nonneg (pow_nonneg (tangentialRate_pos P).le n)
      (mul_nonneg (epsilon_pos P).le (nagumoCoeff_nonneg n))
  · exact firstOrderFormalCoefficients_zero_x P 0
  · intro m n
    exact norm_firstOrderBaseTransport_le P
      (firstOrderFormalCoefficients P) m n
  · intro u v m n huv
    exact firstOrderNonlinearResidual_causal P huv
  · exact hresidual
  · exact firstOrderFormalCoefficients_scaled_recurrence P

theorem nonlinearResidual_diagonalTransportBound
    (P : Params) (u : BivariateStateCoeff) (hu00 : u 0 0 = 0)
    (hu : ∀ i j, ‖u i j‖ ≤
      CKFuchsianMajorant.diagonalTransportEnvelope
        (fun k => epsilon P * nagumoCoeff k)
        (evolutionRate P) (tangentialRate P) i j) :
    ∀ m n,
      ‖firstOrderNonlinearResidual P u m n‖ ≤
        ((m + n).choose m : ℝ) * evolutionRate P ^ m *
          tangentialRate P ^ n * residualProfile P (m + n) := by
  intro m n
  have h :=
    CKNormalizedResidualScaling.norm_firstOrderNonlinearResidual_le_diagonalTransportEnvelope_tangentialRate
      P (R := evolutionRate P) (epsilon := epsilon P)
      (evolutionRate_pos P) (epsilon_pos P)
      (epsilon_small_principal P) (epsilon_small_source P)
      hu00 hu m n
  simpa [CKFuchsianMajorant.diagonalTransportEnvelope,
    residualProfile, firstOrderResidualNagumoProfile,
    pointSourceSize, sourceSlope, quadraticSize, principalSlope,
    tangentialRate, normalizedNagumoProfile] using h

theorem firstOrderFormalCoefficients_diagonalTransportBound (P : Params) :
    ∀ m n, ‖firstOrderFormalCoefficients P m n‖ ≤
      CKFuchsianMajorant.diagonalTransportEnvelope
        (fun k => epsilon P * nagumoCoeff k)
        (evolutionRate P) (tangentialRate P) m n := by
  apply firstOrderFormalCoefficients_diagonalTransportBound_of_residual P
  exact nonlinearResidual_diagonalTransportBound P

theorem firstOrderFormalCoefficients_vectorGeometricBound_of_residual
    (P : Params)
    (hresidual : ∀ u : BivariateStateCoeff, u 0 0 = 0 →
      (∀ i j, ‖u i j‖ ≤
        CKFuchsianMajorant.diagonalTransportEnvelope
          (fun k => epsilon P * nagumoCoeff k)
          (evolutionRate P) (tangentialRate P) i j) →
      ∀ m n,
        ‖firstOrderNonlinearResidual P u m n‖ ≤
          ((m + n).choose m : ℝ) * evolutionRate P ^ m *
            tangentialRate P ^ n * residualProfile P (m + n)) :
    CKVectorAnalyticEvaluation.VectorGeometricBound
      (CKVectorAnalyticEvaluation.stateComponents
        (firstOrderFormalCoefficients P))
      (epsilon P) (2 * evolutionRate P) (2 * tangentialRate P) := by
  let henv := firstOrderFormalCoefficients_diagonalTransportBound_of_residual
    P hresidual
  refine ⟨fun i => ?_⟩
  have hi :=
    CKStableTransportMajorant.geometricBound_component_of_norm_le_diagonalTransportEnvelope
      (a := firstOrderFormalCoefficients P)
      (c := fun k => epsilon P * nagumoCoeff k)
      (C := epsilon P) (T := 1)
      (R := evolutionRate P) (S := tangentialRate P)
      (epsilon_pos P).le (by norm_num) (evolutionRate_pos P).le
      (tangentialRate_pos P).le
      (fun k => by
        simp only [one_pow, mul_one]
        exact mul_le_of_le_one_right (epsilon_pos P).le
          (CKNagumoTransportClosure.nagumoCoeff_le_one k))
      henv i
  change CKGeometricMajorant.GeometricBound
    (fun m n => firstOrderFormalCoefficients P m n i)
      (epsilon P) (2 * evolutionRate P) (2 * tangentialRate P)
  simpa only [mul_one] using hi

theorem firstOrderFormalCoefficients_vectorGeometricBound (P : Params) :
    CKVectorAnalyticEvaluation.VectorGeometricBound
      (CKVectorAnalyticEvaluation.stateComponents
        (firstOrderFormalCoefficients P))
      (epsilon P) (2 * evolutionRate P) (2 * tangentialRate P) := by
  apply firstOrderFormalCoefficients_vectorGeometricBound_of_residual P
  exact nonlinearResidual_diagonalTransportBound P

end
end CKFirstOrderCompleteConvergence
end StressTensor

