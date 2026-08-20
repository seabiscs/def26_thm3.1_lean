import StressTensor.CKBivariateRateNormalization
import StressTensor.CKPolarUniqueness
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# A sharp symmetric representative for bivariate formal series

Ordinary bivariate coefficients determine only the diagonal values of a
formal multilinear series.  This file chooses an explicit symmetric
representative on the `L¹` product of the two scalar variables.  In degree
`k`, a subset `s ⊆ Fin k` records which slots contribute the first
coordinate.  Dividing its coefficient by `k.choose s.card` makes the sum
over all subsets of a fixed size recover the ordinary monomial coefficient.

The `L¹` norm is essential for the sharp estimate: after summing over all
subsets, the scalar weights factor as

`prod i (‖(z i).fst‖ + ‖(z i).snd‖) = prod i ‖z i‖`.

Thus a coefficient estimate by `choose (m+n) m * c (m+n)` gives operator
norm at most `c k`, with no extra exponential loss in `k`.
-/

namespace StressTensor
namespace CKSymmetricBivariateFMS

open CKFirstOrderFormalSystem CKBivariateRateNormalization
open scoped BigOperators ENNReal

noncomputable section

/-- The two scalar variables equipped with their product `L¹` norm. -/
abbrev L1Domain := WithLp 1 (ℝ × ℝ)

/-- The scalar monomial that selects the first coordinate in precisely the
slots belonging to `s`, and the second coordinate in all other slots. -/
def subsetMonomial (k : ℕ) (s : Finset (Fin k)) :
    L1Domain[×k]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ k ℝ).compContinuousLinearMap
    (fun i => if i ∈ s then WithLp.fstL 1 ℝ ℝ ℝ
      else WithLp.sndL 1 ℝ ℝ ℝ)

theorem subsetMonomial_apply (k : ℕ) (s : Finset (Fin k))
    (z : Fin k → L1Domain) :
    subsetMonomial k s z =
      ∏ i, if i ∈ s then (z i).fst else (z i).snd := by
  simp only [subsetMonomial,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases his : i ∈ s <;>
    simp [his, WithLp.fstL_apply, WithLp.sndL_apply]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The symmetric multilinear representative of an ordinary bivariate
coefficient array. -/
def symmBivariateFMS (a : ℕ → ℕ → G) :
    FormalMultilinearSeries ℝ L1Domain G := fun k =>
  ∑ s : Finset (Fin k),
    (subsetMonomial k s).smulRight
      (((k.choose s.card : ℝ)⁻¹) • a s.card (k - s.card))

theorem symmBivariateFMS_apply (a : ℕ → ℕ → G) (k : ℕ)
    (z : Fin k → L1Domain) :
    symmBivariateFMS a k z =
      ∑ s : Finset (Fin k),
        (∏ i, if i ∈ s then (z i).fst else (z i).snd) •
          (((k.choose s.card : ℝ)⁻¹) •
            a s.card (k - s.card)) := by
  rw [symmBivariateFMS, sum_apply]
  apply Finset.sum_congr rfl
  intro s hs
  rw [ContinuousMultilinearMap.smulRight_apply, subsetMonomial_apply]

theorem subsetMonomial_toLp_diag (k : ℕ) (s : Finset (Fin k))
    (x y : ℝ) :
    subsetMonomial k s (fun _ => WithLp.toLp 1 (x, y)) =
      x ^ s.card * y ^ (k - s.card) := by
  rw [subsetMonomial_apply]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  calc
    (∏ i : Fin k, if i ∈ s then x else y) =
        (∏ _i ∈ s, x) * ∏ _i ∈ sᶜ, y := by
      rw [Finset.prod_ite]
      congr 1
      · apply Finset.prod_congr
        · ext i
          simp
        · intro i hi
          rfl
      · apply Finset.prod_congr
        · ext i
          simp
        · intro i hi
          rfl
    _ = x ^ s.card * y ^ (k - s.card) := by
      simp [Finset.card_compl]

/-- On the diagonal, the symmetric representative is exactly the ordinary
homogeneous bivariate polynomial. -/
theorem symmBivariateFMS_apply_diag (a : ℕ → ℕ → G)
    (k : ℕ) (x y : ℝ) :
    symmBivariateFMS a k (fun _ => WithLp.toLp 1 (x, y)) =
      ∑ m ∈ Finset.range (k + 1),
        (x ^ m * y ^ (k - m)) • a m (k - m) := by
  rw [symmBivariateFMS, sum_apply]
  calc
    ∑ s : Finset (Fin k),
        ((subsetMonomial k s).smulRight
          (((k.choose s.card : ℝ)⁻¹) • a s.card (k - s.card)))
          (fun _ => WithLp.toLp 1 (x, y)) =
      ∑ m ∈ Finset.range (k + 1),
        ∑ s ∈ (Finset.univ : Finset (Fin k)).powersetCard m,
          ((subsetMonomial k s).smulRight
            (((k.choose s.card : ℝ)⁻¹) • a s.card (k - s.card)))
            (fun _ => WithLp.toLp 1 (x, y)) := by
      simpa only [Finset.card_univ, Fintype.card_fin,
        Finset.powerset_univ] using
        (Finset.sum_powerset (Finset.univ : Finset (Fin k))
          (fun s => ((subsetMonomial k s).smulRight
            (((k.choose s.card : ℝ)⁻¹) • a s.card (k - s.card)))
            (fun _ => WithLp.toLp 1 (x, y))))
    _ = ∑ m ∈ Finset.range (k + 1),
        (x ^ m * y ^ (k - m)) • a m (k - m) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmk : m ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
      calc
        ∑ s ∈ (Finset.univ : Finset (Fin k)).powersetCard m,
            ((subsetMonomial k s).smulRight
              (((k.choose s.card : ℝ)⁻¹) • a s.card (k - s.card)))
              (fun _ => WithLp.toLp 1 (x, y)) =
          ∑ _s ∈ (Finset.univ : Finset (Fin k)).powersetCard m,
            (x ^ m * y ^ (k - m)) •
              (((k.choose m : ℝ)⁻¹) • a m (k - m)) := by
          apply Finset.sum_congr rfl
          intro s hs
          have hcard : s.card = m := (Finset.mem_powersetCard.mp hs).2
          rw [ContinuousMultilinearMap.smulRight_apply,
            subsetMonomial_toLp_diag, hcard]
        _ = (x ^ m * y ^ (k - m)) • a m (k - m) := by
          rw [Finset.sum_const, Finset.card_powersetCard,
            Finset.card_univ, Fintype.card_fin]
          rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul]
          have hc : (k.choose m : ℝ) ≠ 0 := by
            exact_mod_cast Nat.choose_ne_zero hmk
          congr 1
          field_simp

/-- The product of coordinate norms attached to one subset monomial. -/
def subsetNormWeight (k : ℕ) (s : Finset (Fin k))
    (z : Fin k → L1Domain) : ℝ :=
  ∏ i, if i ∈ s then ‖(z i).fst‖ else ‖(z i).snd‖

theorem sum_subsetNormWeight (k : ℕ) (z : Fin k → L1Domain) :
    ∑ s : Finset (Fin k), subsetNormWeight k s z =
      ∏ i, (‖(z i).fst‖ + ‖(z i).snd‖) := by
  calc
    ∑ s : Finset (Fin k), subsetNormWeight k s z =
        ∑ s ∈ (Finset.univ : Finset (Fin k)).powerset,
          (∏ i ∈ s, ‖(z i).fst‖) *
            ∏ i ∈ (Finset.univ : Finset (Fin k)) \ s, ‖(z i).snd‖ := by
      rw [Finset.powerset_univ]
      apply Finset.sum_congr rfl
      intro s hs
      unfold subsetNormWeight
      rw [Finset.prod_ite]
      congr 1
      · apply Finset.prod_congr
        · ext i
          simp
        · intro i hi
          rfl
      · apply Finset.prod_congr
        · ext i
          simp
        · intro i hi
          rfl
    _ = ∏ i, (‖(z i).fst‖ + ‖(z i).snd‖) := by
      symm
      exact Finset.prod_add _ _ Finset.univ

theorem norm_scaledCoefficient_le
    (a : ℕ → ℕ → G) (c : ℕ → ℝ)
    (ha : ∀ m n, ‖a m n‖ ≤ ((m + n).choose m : ℝ) * c (m + n))
    (k : ℕ) (s : Finset (Fin k)) :
    ‖((k.choose s.card : ℝ)⁻¹ • a s.card (k - s.card))‖ ≤ c k := by
  have hcard : s.card ≤ k := by
    simpa using Finset.card_le_univ s
  have hsum : s.card + (k - s.card) = k := Nat.add_sub_of_le hcard
  have hchoose : 0 < (k.choose s.card : ℝ) := by
    exact_mod_cast Nat.choose_pos hcard
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hchoose]
  calc
    (k.choose s.card : ℝ)⁻¹ * ‖a s.card (k - s.card)‖ ≤
        (k.choose s.card : ℝ)⁻¹ *
          ((k.choose s.card : ℝ) * c k) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [hsum] using ha s.card (k - s.card)
      · positivity
    _ = c k := by
      field_simp

theorem abs_subsetMonomial_apply
    (k : ℕ) (s : Finset (Fin k)) (z : Fin k → L1Domain) :
    |subsetMonomial k s z| = subsetNormWeight k s z := by
  rw [subsetMonomial_apply]
  unfold subsetNormWeight
  calc
    |∏ i, if i ∈ s then (z i).fst else (z i).snd| =
        ∏ i, |if i ∈ s then (z i).fst else (z i).snd| := by
      exact Finset.abs_prod Finset.univ _
    _ = ∏ i, if i ∈ s then ‖(z i).fst‖ else ‖(z i).snd‖ := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases his : i ∈ s <;> simp [his, Real.norm_eq_abs]

theorem subsetNormWeight_nonneg
    (k : ℕ) (s : Finset (Fin k)) (z : Fin k → L1Domain) :
    0 ≤ subsetNormWeight k s z := by
  unfold subsetNormWeight
  positivity

/-- Pointwise form of the sharp `L¹` multilinear estimate. -/
theorem norm_symmBivariateFMS_apply_le
    (a : ℕ → ℕ → G) (c : ℕ → ℝ)
    (ha : ∀ m n, ‖a m n‖ ≤ ((m + n).choose m : ℝ) * c (m + n))
    (k : ℕ) (z : Fin k → L1Domain) :
    ‖symmBivariateFMS a k z‖ ≤ c k * ∏ i, ‖z i‖ := by
  have hc : 0 ≤ c k := by
    have h0 := ha 0 k
    simpa using (norm_nonneg (a 0 k)).trans h0
  rw [symmBivariateFMS, sum_apply]
  calc
    ‖∑ s : Finset (Fin k),
        ((subsetMonomial k s).smulRight
          (((k.choose s.card : ℝ)⁻¹) • a s.card (k - s.card))) z‖ ≤
      ∑ s : Finset (Fin k),
        ‖((subsetMonomial k s).smulRight
          (((k.choose s.card : ℝ)⁻¹) • a s.card (k - s.card))) z‖ :=
      norm_sum_le _ _
    _ ≤ ∑ s : Finset (Fin k), subsetNormWeight k s z * c k := by
      apply Finset.sum_le_sum
      intro s hs
      rw [ContinuousMultilinearMap.smulRight_apply, norm_smul,
        Real.norm_eq_abs, abs_subsetMonomial_apply]
      exact mul_le_mul_of_nonneg_left
        (norm_scaledCoefficient_le a c ha k s)
        (subsetNormWeight_nonneg k s z)
    _ = c k * ∏ i, ‖z i‖ := by
      rw [← Finset.sum_mul, sum_subsetNormWeight]
      simp_rw [← WithLp.prod_norm_eq_of_L1 (z _)]
      ring

/-- Sharp operator-norm estimate for the symmetric representative. -/
theorem norm_symmBivariateFMS_le
    (a : ℕ → ℕ → G) (c : ℕ → ℝ)
    (ha : ∀ m n, ‖a m n‖ ≤ ((m + n).choose m : ℝ) * c (m + n))
    (k : ℕ) :
    ‖symmBivariateFMS a k‖ ≤ c k := by
  have hc : 0 ≤ c k := by
    have h0 := ha 0 k
    simpa using (norm_nonneg (a 0 k)).trans h0
  exact ContinuousMultilinearMap.opNorm_le_bound hc
    (norm_symmBivariateFMS_apply_le a c ha k)

/-! ## State-valued specialization -/

/-- The symmetric `L¹` representative of an ordinary state coefficient
array. -/
def symmStateFMS (a : BivariateStateCoeff) :
    FormalMultilinearSeries ℝ L1Domain FirstOrderState :=
  symmBivariateFMS a

/-- The new symmetric representative and the existing canonical bivariate
FMS have identical diagonal homogeneous values. -/
theorem symmStateFMS_apply_diag_eq_stateBivariateFMS
    (a : BivariateStateCoeff) (k : ℕ) (x y : ℝ) :
    symmStateFMS a k (fun _ => WithLp.toLp 1 (x, y)) =
      stateBivariateFMS a k (fun _ => (x, y)) := by
  rw [symmStateFMS, symmBivariateFMS_apply_diag,
    CKPolarUniqueness.stateBivariateFMS_apply_diag]

theorem norm_symmStateFMS_le
    (a : BivariateStateCoeff) (c : ℕ → ℝ)
    (ha : ∀ m n, ‖a m n‖ ≤ ((m + n).choose m : ℝ) * c (m + n))
    (k : ℕ) :
    ‖symmStateFMS a k‖ ≤ c k := by
  exact norm_symmBivariateFMS_le a c ha k

/-- A diagonal transport envelope becomes a sharp homogeneous operator-norm
bound after rate normalization and `L¹` symmetrization. -/
theorem norm_symmStateFMS_normalizeStateCoeff_le
    {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    {a : BivariateStateCoeff} {c : ℕ → ℝ}
    (hc : ∀ k, 0 ≤ c k)
    (ha : ∀ m n,
      ‖a m n‖ ≤
        CKFuchsianMajorant.diagonalTransportEnvelope c R S m n)
    (k : ℕ) :
    ‖symmStateFMS (normalizeStateCoeff R S a) k‖ ≤ c k := by
  apply norm_symmStateFMS_le
  exact norm_normalizeStateCoeff_le hR hS hc ha

end
end CKSymmetricBivariateFMS
end StressTensor
