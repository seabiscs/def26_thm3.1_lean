import StressTensor.CKSymmetricBivariateFMS
import StressTensor.CKPolarScaling
import StressTensor.CKFirstOrderConvergence

/-!
# Rate-normalized state, phase, and Euler series

The sharp symmetric representative is naturally estimated after the two
geometric coefficient rates have been removed.  This file constructs the
corresponding normalized state, phase, and Euler FMS on the `L¹` product
domain and proves that the inverse change of variables restores the existing
physical formal series exactly on every diagonal homogeneous value.

The normalized phase has coordinates `(Y / S, U₀, U₁)`.  Consequently,
its first-coordinate coefficient is `S⁻¹` in bidegree `(0,1)` and zero
elsewhere.  The normalized Euler series has coefficient `n • a m n` in
bidegree `(m,n)`.
-/

namespace StressTensor
namespace CKNormalizedPhase

open CKFirstOrderFormalSystem CKBivariateRateNormalization
  CKSymmetricBivariateFMS
open scoped BigOperators ENNReal

noncomputable section

/-! ## Definitions -/

/-- Restore the geometric rates in the two input variables and regard the
result as an element of the `L¹` product domain. -/
def weightedDomainMap (R S : ℝ) : Domain →L[ℝ] L1Domain :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ ℝ ℝ).symm.toContinuousLinearMap.comp
    ((R • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (S • ContinuousLinearMap.snd ℝ ℝ ℝ))

@[simp] theorem weightedDomainMap_apply (R S : ℝ) (z : Domain) :
    weightedDomainMap R S z = WithLp.toLp 1 (R * z.1, S * z.2) := by
  rfl

/-- Coefficients of the normalized phase `(Y/S, U₀, U₁)`. -/
def normalizedPhaseCoeff (S : ℝ) (a : BivariateStateCoeff) :
    ℕ → ℕ → FirstOrderPhase := fun m n =>
  Fin.cases (if m = 0 ∧ n = 1 then S⁻¹ else 0)
    (fun j : Fin 2 => a m n j)

/-- Coefficients of the physical phase `(y, U₀, U₁)`. -/
def phaseCoefficientArray (a : BivariateStateCoeff) :
    ℕ → ℕ → FirstOrderPhase := fun m n =>
  Fin.cases (if m = 0 ∧ n = 1 then 1 else 0)
    (fun j : Fin 2 => a m n j)

/-- Symmetric `L¹` representative of the normalized phase. -/
def normalizedPhaseFMS (S : ℝ) (a : BivariateStateCoeff) :
    FormalMultilinearSeries ℝ L1Domain FirstOrderPhase :=
  symmBivariateFMS (normalizedPhaseCoeff S a)

/-- Symmetric `L¹` representative of the normalized state. -/
def normalizedStateFMS (a : BivariateStateCoeff) :
    FormalMultilinearSeries ℝ L1Domain FirstOrderState :=
  symmStateFMS a

/-- Symmetric `L¹` representative of the normalized Euler field
`Y ∂Y U`, whose `(m,n)` coefficient is `n a[m,n]`. -/
def normalizedEulerFMS (a : BivariateStateCoeff) :
    FormalMultilinearSeries ℝ L1Domain FirstOrderState :=
  symmStateFMS (fun m n => (n : ℝ) • a m n)

/-! ## Zero coefficient and sharp norm bounds -/

/-- If the state has zero constant coefficient, then so does its phase. -/
theorem normalizedPhaseFMS_zero
    (S : ℝ) {a : BivariateStateCoeff} (ha : a 0 0 = 0) :
    normalizedPhaseFMS S a 0 = 0 := by
  ext z i
  have hz : z = fun _ => WithLp.toLp 1 ((0 : ℝ), (0 : ℝ)) :=
    Subsingleton.elim _ _
  rw [hz, normalizedPhaseFMS, symmBivariateFMS_apply_diag]
  fin_cases i <;> simp [normalizedPhaseCoeff, ha] <;> rfl

/-- The normalized state inherits the sharp homogeneous bound from its
ordinary bivariate coefficients. -/
theorem norm_normalizedStateFMS_le
    (a : BivariateStateCoeff) (ε : ℝ) (φ : ℕ → ℝ)
    (ha : ∀ m n,
      ‖a m n‖ ≤ ((m + n).choose m : ℝ) * (ε * φ (m + n)))
    (k : ℕ) :
    ‖normalizedStateFMS a k‖ ≤ ε * φ k := by
  exact norm_symmStateFMS_le a (fun n => ε * φ n) ha k

/-- The sparse `Y/S` coordinate and the two state coordinates obey the same
binomial coefficient bound. -/
theorem norm_normalizedPhaseCoeff_le
    {S : ℝ} (hS : 0 < S)
    (a : BivariateStateCoeff) (ε : ℝ) (φ : ℕ → ℝ)
    (ha : ∀ m n,
      ‖a m n‖ ≤ ((m + n).choose m : ℝ) * (ε * φ (m + n)))
    (hy : S⁻¹ ≤ ε * φ 1)
    (m n : ℕ) :
    ‖normalizedPhaseCoeff S a m n‖ ≤
      ((m + n).choose m : ℝ) * (ε * φ (m + n)) := by
  have htarget :
      0 ≤ ((m + n).choose m : ℝ) * (ε * φ (m + n)) :=
    (norm_nonneg (a m n)).trans (ha m n)
  rw [pi_norm_le_iff_of_nonneg htarget]
  intro i
  fin_cases i
  · simp only [normalizedPhaseCoeff]
    split_ifs with hmn
    · rcases hmn with ⟨rfl, rfl⟩
      change |S⁻¹| ≤ _
      rw [abs_of_pos (inv_pos.mpr hS)]
      simpa using hy
    · simp [htarget]
  · change ‖a m n (0 : Fin 2)‖ ≤ _
    exact (norm_le_pi_norm (a m n) 0).trans (ha m n)
  · change ‖a m n (1 : Fin 2)‖ ≤ _
    exact (norm_le_pi_norm (a m n) 1).trans (ha m n)

/-- Sharp homogeneous norm bound for the normalized phase. -/
theorem norm_normalizedPhaseFMS_le
    {S : ℝ} (hS : 0 < S)
    (a : BivariateStateCoeff) (ε : ℝ) (φ : ℕ → ℝ)
    (ha : ∀ m n,
      ‖a m n‖ ≤ ((m + n).choose m : ℝ) * (ε * φ (m + n)))
    (hy : S⁻¹ ≤ ε * φ 1)
    (k : ℕ) :
    ‖normalizedPhaseFMS S a k‖ ≤ ε * φ k := by
  apply norm_symmBivariateFMS_le
  exact norm_normalizedPhaseCoeff_le hS a ε φ ha hy

/-- The Euler factor costs at most the total degree `k`. -/
theorem norm_normalizedEulerFMS_le
    (a : BivariateStateCoeff) (ε : ℝ) (φ : ℕ → ℝ)
    (ha : ∀ m n,
      ‖a m n‖ ≤ ((m + n).choose m : ℝ) * (ε * φ (m + n)))
    (k : ℕ) :
    ‖normalizedEulerFMS a k‖ ≤ ε * (k : ℝ) * φ k := by
  unfold normalizedEulerFMS
  apply norm_symmStateFMS_le
  intro m n
  have hchoose : 0 < ((m + n).choose m : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_right m n)
  have hprofile : 0 ≤ ε * φ (m + n) :=
    nonneg_of_mul_nonneg_right
      ((norm_nonneg (a m n)).trans (ha m n)) hchoose
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
  calc
    (n : ℝ) * ‖a m n‖ ≤
        (n : ℝ) *
          (((m + n).choose m : ℝ) * (ε * φ (m + n))) := by
      exact mul_le_mul_of_nonneg_left (ha m n) (Nat.cast_nonneg n)
    _ ≤ (m + n : ℝ) *
          (((m + n).choose m : ℝ) * (ε * φ (m + n))) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.le_add_left n m
      · exact mul_nonneg hchoose.le hprofile
    _ = ((m + n).choose m : ℝ) *
          (((m + n : ℕ) : ℝ) * (ε * φ (m + n))) := by
      rw [Nat.cast_add]
      ring
    _ = ((m + n).choose m : ℝ) *
          (ε * ((m + n : ℕ) : ℝ) * φ (m + n)) := by
      ring

/-! ## Exact diagonal restoration -/

/-- The symmetric FMS built from the physical phase coefficient array has
the same diagonal values as the existing canonical `phaseSeries`. -/
theorem phaseCoefficientFMS_apply_diag_eq_phaseSeries
    (a : BivariateStateCoeff) (k : ℕ) (x y : ℝ) :
    symmBivariateFMS (phaseCoefficientArray a) k
        (fun _ => WithLp.toLp 1 (x, y)) =
      phaseSeries (stateBivariateFMS a) k
        (fun _ : Fin k => (x, y)) := by
  rw [symmBivariateFMS_apply_diag]
  ext i
  simp only [phaseSeries, FormalMultilinearSeries.pi,
    ContinuousMultilinearMap.pi_apply]
  refine Fin.cases ?_ (fun j => ?_) i
  · cases k with
    | zero => simp [phaseCoefficientArray, ySeries, linearSeries]
    | succ k =>
        cases k with
        | zero =>
            norm_num [phaseCoefficientArray, ySeries, linearSeries,
              Finset.sum_range_succ, yProjection]
            change y = y
            rfl
        | succ k =>
            simp only [phaseCoefficientArray, Finset.sum_apply,
              Pi.smul_apply, Fin.cases_zero, smul_eq_mul, ySeries,
              linearSeries]
            apply Finset.sum_eq_zero
            intro m hm
            by_cases hcond : m = 0 ∧ k + 1 + 1 - m = 1
            · rcases hcond with ⟨rfl, h⟩
              omega
            · simp [hcond]
  · simp only [Finset.sum_apply, Pi.smul_apply,
      phaseCoefficientArray, Fin.cases_succ]
    simp [stateComponent,
      CKPolarUniqueness.stateBivariateFMS_apply_diag]

/-- Restoring the rates in one normalized phase coefficient gives the
corresponding physical phase coefficient exactly. -/
theorem rate_smul_normalizedPhaseCoeff_normalizeStateCoeff
    {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (a : BivariateStateCoeff) (m n : ℕ) :
    (R ^ m * S ^ n) •
        normalizedPhaseCoeff S (normalizeStateCoeff R S a) m n =
      phaseCoefficientArray a m n := by
  ext i
  fin_cases i
  · simp only [Pi.smul_apply, normalizedPhaseCoeff,
      phaseCoefficientArray]
    by_cases hmn : m = 0 ∧ n = 1
    · rcases hmn with ⟨rfl, rfl⟩
      simp [hS.ne']
    · simp [hmn]
  · change
      ((R ^ m * S ^ n) • normalizeStateCoeff R S a m n) (0 : Fin 2) =
        a m n 0
    exact congrFun
      (denormalizeStateCoeff_apply_normalize hR hS a m n) 0
  · change
      ((R ^ m * S ^ n) • normalizeStateCoeff R S a m n) (1 : Fin 2) =
        a m n 1
    exact congrFun
      (denormalizeStateCoeff_apply_normalize hR hS a m n) 1

/-- Composing the normalized state with the weighted input map restores the
canonical physical state series on every diagonal homogeneous value. -/
theorem normalizedStateFMS_comp_weightedDomainMap_apply_diag
    {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (a : BivariateStateCoeff) (k : ℕ) (x y : ℝ) :
    (normalizedStateFMS (normalizeStateCoeff R S a)).compContinuousLinearMap
        (weightedDomainMap R S) k (fun _ : Fin k => (x, y)) =
      stateBivariateFMS a k (fun _ : Fin k => (x, y)) := by
  rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
  change
    symmStateFMS (normalizeStateCoeff R S a) k
        (fun _ => weightedDomainMap R S (x, y)) = _
  simp only [weightedDomainMap_apply]
  rw [symmStateFMS_apply_diag_eq_stateBivariateFMS,
    CKPolarUniqueness.stateBivariateFMS_apply_diag,
    CKPolarUniqueness.stateBivariateFMS_apply_diag]
  apply Finset.sum_congr rfl
  intro m hm
  have hmk : m ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
  let n := k - m
  change
    ((R * x) ^ m * (S * y) ^ n) •
        normalizeStateCoeff R S a m n =
      (x ^ m * y ^ n) • a m n
  calc
    ((R * x) ^ m * (S * y) ^ n) •
        normalizeStateCoeff R S a m n =
      (x ^ m * y ^ n) •
        ((R ^ m * S ^ n) • normalizeStateCoeff R S a m n) := by
      rw [mul_pow, mul_pow, smul_smul]
      congr 1
      ring
    _ = (x ^ m * y ^ n) • a m n := by
      rw [denormalizeStateCoeff_apply_normalize hR hS]

/-- Composing the normalized phase with the weighted input map restores the
canonical physical phase series on every diagonal homogeneous value. -/
theorem normalizedPhaseFMS_comp_weightedDomainMap_apply_diag
    {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (a : BivariateStateCoeff) (k : ℕ) (x y : ℝ) :
    (normalizedPhaseFMS S
        (normalizeStateCoeff R S a)).compContinuousLinearMap
          (weightedDomainMap R S) k (fun _ : Fin k => (x, y)) =
      phaseSeries (stateBivariateFMS a) k
        (fun _ : Fin k => (x, y)) := by
  rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
  change
    normalizedPhaseFMS S (normalizeStateCoeff R S a) k
        (fun _ => weightedDomainMap R S (x, y)) = _
  simp only [weightedDomainMap_apply]
  calc
    normalizedPhaseFMS S (normalizeStateCoeff R S a) k
        (fun _ => WithLp.toLp 1 (R * x, S * y)) =
      symmBivariateFMS (phaseCoefficientArray a) k
        (fun _ => WithLp.toLp 1 (x, y)) := by
      rw [normalizedPhaseFMS, symmBivariateFMS_apply_diag,
        symmBivariateFMS_apply_diag]
      apply Finset.sum_congr rfl
      intro m hm
      have hmk : m ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
      let n := k - m
      change
        ((R * x) ^ m * (S * y) ^ n) •
            normalizedPhaseCoeff S (normalizeStateCoeff R S a) m n =
          (x ^ m * y ^ n) • phaseCoefficientArray a m n
      calc
        ((R * x) ^ m * (S * y) ^ n) •
            normalizedPhaseCoeff S (normalizeStateCoeff R S a) m n =
          (x ^ m * y ^ n) •
            ((R ^ m * S ^ n) •
              normalizedPhaseCoeff S
                (normalizeStateCoeff R S a) m n) := by
          rw [mul_pow, mul_pow, smul_smul]
          congr 1
          ring
        _ = (x ^ m * y ^ n) • phaseCoefficientArray a m n := by
          rw [rate_smul_normalizedPhaseCoeff_normalizeStateCoeff hR hS]
    _ = phaseSeries (stateBivariateFMS a) k
          (fun _ : Fin k => (x, y)) :=
      phaseCoefficientFMS_apply_diag_eq_phaseSeries a k x y

/-- Rate normalization commutes with the ordinary Euler coefficient factor. -/
theorem normalizeStateCoeff_eulerCoefficientArray
    (R S : ℝ) (a : BivariateStateCoeff) :
    normalizeStateCoeff R S
        (CKFirstOrderConvergence.eulerCoefficientArray a) =
      fun (m n : ℕ) =>
        (n : ℝ) • normalizeStateCoeff R S a m n := by
  funext m n
  simp only [normalizeStateCoeff,
    CKFirstOrderConvergence.eulerCoefficientArray]
  rw [smul_smul, smul_smul]
  congr 1
  ring

/-- Composing the normalized Euler FMS with the weighted input map restores
the existing coefficient-local physical Euler series on every diagonal
homogeneous value. -/
theorem normalizedEulerFMS_comp_weightedDomainMap_apply_diag
    {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (a : BivariateStateCoeff) (k : ℕ) (x y : ℝ) :
    (normalizedEulerFMS (normalizeStateCoeff R S a)).compContinuousLinearMap
        (weightedDomainMap R S) k (fun _ : Fin k => (x, y)) =
      formalEulerY (stateBivariateFMS a) k
        (fun _ : Fin k => (x, y)) := by
  calc
    (normalizedEulerFMS
        (normalizeStateCoeff R S a)).compContinuousLinearMap
          (weightedDomainMap R S) k (fun _ : Fin k => (x, y)) =
      (normalizedStateFMS
          (normalizeStateCoeff R S
            (CKFirstOrderConvergence.eulerCoefficientArray a))).compContinuousLinearMap
        (weightedDomainMap R S) k (fun _ : Fin k => (x, y)) := by
        rw [normalizeStateCoeff_eulerCoefficientArray]
        rfl
    _ = stateBivariateFMS
        (CKFirstOrderConvergence.eulerCoefficientArray a) k
          (fun _ : Fin k => (x, y)) :=
      normalizedStateFMS_comp_weightedDomainMap_apply_diag hR hS _ k x y
    _ = formalEulerY (stateBivariateFMS a) k
          (fun _ : Fin k => (x, y)) :=
      (CKFirstOrderConvergence.formalEulerY_stateBivariateFMS_apply_diag
        a k x y).symm

end
end CKNormalizedPhase
end StressTensor
