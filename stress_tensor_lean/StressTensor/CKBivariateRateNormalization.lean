import StressTensor.CKFirstOrderFormalSystem
import StressTensor.CKFuchsianMajorant

/-!
# Scaling out anisotropic bivariate growth rates

The convergent-majorant proof uses an `L¹`-symmetrized homogeneous series
after removing the separate geometric rates in the evolution and tangential
variables.  This file contains the elementary coefficient-level scaling
facts, independently of the chosen multilinear representative.
-/

namespace StressTensor
namespace CKBivariateRateNormalization

open CKFirstOrderFormalSystem CKFuchsianMajorant

noncomputable section

/-- Remove the rates `R^m S^n` from a state coefficient array. -/
def normalizeStateCoeff (R S : ℝ) (a : BivariateStateCoeff) :
    BivariateStateCoeff :=
  fun m n => (R ^ m * S ^ n)⁻¹ • a m n

/-- Restore the rates `R^m S^n` to a normalized array. -/
def denormalizeStateCoeff (R S : ℝ) (a : BivariateStateCoeff) :
    BivariateStateCoeff :=
  fun m n => (R ^ m * S ^ n) • a m n

theorem denormalize_normalize
    {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (a : BivariateStateCoeff) :
    denormalizeStateCoeff R S (normalizeStateCoeff R S a) = a := by
  funext m n
  unfold denormalizeStateCoeff normalizeStateCoeff
  rw [smul_smul]
  have hfac : R ^ m * S ^ n ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hR.ne') (pow_ne_zero _ hS.ne')
  rw [mul_inv_cancel₀ hfac, one_smul]

theorem normalize_denormalize
    {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (a : BivariateStateCoeff) :
    normalizeStateCoeff R S (denormalizeStateCoeff R S a) = a := by
  funext m n
  unfold denormalizeStateCoeff normalizeStateCoeff
  rw [smul_smul]
  have hfac : R ^ m * S ^ n ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hR.ne') (pow_ne_zero _ hS.ne')
  rw [inv_mul_cancel₀ hfac, one_smul]

theorem normalizeStateCoeff_zero
    (R S : ℝ) {a : BivariateStateCoeff} (ha : a 0 0 = 0) :
    normalizeStateCoeff R S a 0 0 = 0 := by
  simp [normalizeStateCoeff, ha]

/-- A diagonal transport envelope becomes a rate-free binomial estimate. -/
theorem norm_normalizeStateCoeff_le
    {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    {a : BivariateStateCoeff} {c : ℕ → ℝ}
    (hc : ∀ k, 0 ≤ c k)
    (ha : ∀ m n,
      ‖a m n‖ ≤ diagonalTransportEnvelope c R S m n) :
    ∀ m n,
      ‖normalizeStateCoeff R S a m n‖ ≤
        ((m + n).choose m : ℝ) * c (m + n) := by
  intro m n
  let d : ℝ := R ^ m * S ^ n
  have hd : 0 < d := mul_pos (pow_pos hR _) (pow_pos hS _)
  have hbase : 0 ≤ ((m + n).choose m : ℝ) * c (m + n) :=
    mul_nonneg (Nat.cast_nonneg _) (hc _)
  unfold normalizeStateCoeff
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
  rw [inv_mul_le_iff₀ hd]
  calc
    ‖a m n‖ ≤ diagonalTransportEnvelope c R S m n := ha m n
    _ = d * (((m + n).choose m : ℝ) * c (m + n)) := by
      dsimp [d]
      unfold diagonalTransportEnvelope
      ring
    _ ≤ d * (((m + n).choose m : ℝ) * c (m + n)) := le_rfl

/-- Rate restoration is exact coefficientwise. -/
theorem denormalizeStateCoeff_apply_normalize
    {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (a : BivariateStateCoeff) (m n : ℕ) :
    (R ^ m * S ^ n) • normalizeStateCoeff R S a m n = a m n := by
  have h := congrFun (congrFun (denormalize_normalize hR hS a) m) n
  exact h

end
end CKBivariateRateNormalization
end StressTensor
