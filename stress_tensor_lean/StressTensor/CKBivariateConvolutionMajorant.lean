import StressTensor.CKFuchsianMajorant
import StressTensor.CKFirstOrderAnalyticData

/-!
# Bivariate Cauchy products and diagonal majorants

This file connects actual two-variable coefficient products to the scalar
diagonal convolution used by the Fuchsian/Catalan closure.  The central exact
identity is

`diagonalLift c * diagonalLift d = diagonalLift (convolution c d)`.

It is proved from the formal Leibniz rule and the fact that a coefficient
array whose formal `x`- and `y`-derivatives agree is uniquely determined by
its zeroth `x` row.  Thus the binomial combinatorics are exposed explicitly,
rather than hidden behind a convergence or evaluation argument.
-/

namespace StressTensor

namespace CKBivariateConvolutionMajorant

open CKPowerSeries CKSeriesBridge CKGeometricMajorant CKDiagonalMajorant
  CKFuchsianMajorant

noncomputable section

/-- The ordinary Cauchy product of two bivariate coefficient arrays. -/
def cauchyProduct (a b : Coeff) : Coeff :=
  fun m n =>
    ∑ ij ∈ Finset.antidiagonal m,
      ∑ kl ∈ Finset.antidiagonal n,
        a ij.1 kl.1 * b ij.2 kl.2

@[simp] theorem cauchyProduct_zero_x (a b : Coeff) (n : ℕ) :
    cauchyProduct a b 0 n = convolution (a 0) (b 0) n := by
  simp [cauchyProduct, convolution]

/-- Splitting the total degree on an antidiagonal gives the coefficient form
of the product rule. -/
theorem succ_mul_sum_antidiagonal (f : ℕ → ℕ → ℝ) (n : ℕ) :
    (n + 1 : ℝ) *
        (∑ ij ∈ Finset.antidiagonal (n + 1), f ij.1 ij.2) =
      (∑ ij ∈ Finset.antidiagonal n,
        (ij.1 + 1 : ℝ) * f (ij.1 + 1) ij.2) +
      ∑ ij ∈ Finset.antidiagonal n,
        (ij.2 + 1 : ℝ) * f ij.1 (ij.2 + 1) := by
  rw [Finset.mul_sum]
  calc
    ∑ ij ∈ Finset.antidiagonal (n + 1), (n + 1 : ℝ) * f ij.1 ij.2 =
        ∑ ij ∈ Finset.antidiagonal (n + 1),
          ((ij.1 : ℝ) * f ij.1 ij.2 + (ij.2 : ℝ) * f ij.1 ij.2) := by
      apply Finset.sum_congr rfl
      intro ij hij
      have hadd : ij.1 + ij.2 = n + 1 := Finset.mem_antidiagonal.mp hij
      have haddR : (ij.1 : ℝ) + (ij.2 : ℝ) = (n + 1 : ℝ) := by
        exact_mod_cast hadd
      rw [← haddR]
      ring
    _ = (∑ ij ∈ Finset.antidiagonal (n + 1),
          (ij.1 : ℝ) * f ij.1 ij.2) +
        ∑ ij ∈ Finset.antidiagonal (n + 1),
          (ij.2 : ℝ) * f ij.1 ij.2 := by
      rw [Finset.sum_add_distrib]
    _ = (∑ ij ∈ Finset.antidiagonal n,
          (ij.1 + 1 : ℝ) * f (ij.1 + 1) ij.2) +
        ∑ ij ∈ Finset.antidiagonal n,
          (ij.2 + 1 : ℝ) * f ij.1 (ij.2 + 1) := by
      congr 1
      · rw [Finset.Nat.sum_antidiagonal_succ]
        simp
      · rw [Finset.Nat.sum_antidiagonal_succ']
        simp

/-- Formal differentiation obeys the Leibniz rule for scalar Cauchy
convolution. -/
theorem derivativeScalar_convolution (c d : ℕ → ℝ) :
    derivativeScalar (convolution c d) =
      fun n => convolution (derivativeScalar c) d n +
        convolution c (derivativeScalar d) n := by
  funext n
  simp only [derivativeScalar, convolution]
  calc
    (n + 1 : ℝ) *
        (∑ ij ∈ Finset.antidiagonal (n + 1), c ij.1 * d ij.2) =
        (∑ ij ∈ Finset.antidiagonal n,
          (ij.1 + 1 : ℝ) * (c (ij.1 + 1) * d ij.2)) +
        ∑ ij ∈ Finset.antidiagonal n,
          (ij.2 + 1 : ℝ) * (c ij.1 * d (ij.2 + 1)) :=
      succ_mul_sum_antidiagonal (fun i j => c i * d j) n
    _ = (∑ ij ∈ Finset.antidiagonal n,
          (ij.1 + 1 : ℝ) * c (ij.1 + 1) * d ij.2) +
        ∑ ij ∈ Finset.antidiagonal n,
          c ij.1 * ((ij.2 + 1 : ℝ) * d (ij.2 + 1)) := by
      congr 1 <;> apply Finset.sum_congr rfl <;> intro ij hij <;> ring

/-- Formal `x` differentiation obeys the Leibniz rule for the bivariate
Cauchy product. -/
theorem coeffX_cauchyProduct (a b : Coeff) :
    coeffX (cauchyProduct a b) =
      fun m n => cauchyProduct (coeffX a) b m n +
        cauchyProduct a (coeffX b) m n := by
  funext m n
  simp only [coeffX, cauchyProduct]
  calc
    (m + 1 : ℝ) *
        (∑ ij ∈ Finset.antidiagonal (m + 1),
          ∑ kl ∈ Finset.antidiagonal n,
            a ij.1 kl.1 * b ij.2 kl.2) =
        (∑ ij ∈ Finset.antidiagonal m,
          (ij.1 + 1 : ℝ) *
            (∑ kl ∈ Finset.antidiagonal n,
              a (ij.1 + 1) kl.1 * b ij.2 kl.2)) +
        ∑ ij ∈ Finset.antidiagonal m,
          (ij.2 + 1 : ℝ) *
            (∑ kl ∈ Finset.antidiagonal n,
              a ij.1 kl.1 * b (ij.2 + 1) kl.2) :=
      succ_mul_sum_antidiagonal
        (fun i j => ∑ kl ∈ Finset.antidiagonal n,
          a i kl.1 * b j kl.2) m
    _ = (∑ ij ∈ Finset.antidiagonal m,
          ∑ kl ∈ Finset.antidiagonal n,
            (ij.1 + 1 : ℝ) * a (ij.1 + 1) kl.1 * b ij.2 kl.2) +
        ∑ ij ∈ Finset.antidiagonal m,
          ∑ kl ∈ Finset.antidiagonal n,
            a ij.1 kl.1 * ((ij.2 + 1 : ℝ) * b (ij.2 + 1) kl.2) := by
      congr 1 <;> apply Finset.sum_congr rfl <;> intro ij hij <;>
        rw [Finset.mul_sum] <;> apply Finset.sum_congr rfl <;>
        intro kl hkl <;> ring

/-- Formal `y` differentiation obeys the Leibniz rule for the bivariate
Cauchy product. -/
theorem coeffY_cauchyProduct (a b : Coeff) :
    coeffY (cauchyProduct a b) =
      fun m n => cauchyProduct (coeffY a) b m n +
        cauchyProduct a (coeffY b) m n := by
  funext m n
  simp only [coeffY, cauchyProduct]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  calc
    (n + 1 : ℝ) *
        (∑ kl ∈ Finset.antidiagonal (n + 1),
          a ij.1 kl.1 * b ij.2 kl.2) =
        (∑ kl ∈ Finset.antidiagonal n,
          (kl.1 + 1 : ℝ) * (a ij.1 (kl.1 + 1) * b ij.2 kl.2)) +
        ∑ kl ∈ Finset.antidiagonal n,
          (kl.2 + 1 : ℝ) * (a ij.1 kl.1 * b ij.2 (kl.2 + 1)) :=
      succ_mul_sum_antidiagonal
        (fun k l => a ij.1 k * b ij.2 l) n
    _ = (∑ kl ∈ Finset.antidiagonal n,
          (kl.1 + 1 : ℝ) * a ij.1 (kl.1 + 1) * b ij.2 kl.2) +
        ∑ kl ∈ Finset.antidiagonal n,
          a ij.1 kl.1 * ((kl.2 + 1 : ℝ) * b ij.2 (kl.2 + 1)) := by
      congr 1 <;> apply Finset.sum_congr rfl <;> intro kl hkl <;> ring

/-- Equality of the two formal derivatives, together with the zeroth `x`
row, characterizes a diagonal lift. -/
theorem eq_diagonalLift_of_coeffX_eq_coeffY
    (a : Coeff) (c : ℕ → ℝ)
    (hzero : ∀ n, a 0 n = c n)
    (hderiv : coeffX a = coeffY a) :
    a = diagonalLift c := by
  funext m n
  induction m generalizing n with
  | zero => simpa [diagonalLift] using hzero n
  | succ m ih =>
      have hxy := congrFun (congrFun hderiv m) n
      simp only [coeffX, coeffY] at hxy
      have hchooseNat :
          (m + 1) * (m + n + 1).choose (m + 1) =
            (n + 1) * (m + n + 1).choose m := by
        calc
          (m + 1) * (m + n + 1).choose (m + 1) =
              (m + n + 1).choose (m + 1) * (m + 1) := Nat.mul_comm _ _
          _ = (m + n + 1).choose m * (n + 1) := by
            rw [Nat.choose_succ_right_eq]
            congr 1
            omega
          _ = (n + 1) * (m + n + 1).choose m := Nat.mul_comm _ _
      have hchoose :
          (m + 1 : ℝ) * ((m + n + 1).choose (m + 1) : ℝ) =
            (n + 1 : ℝ) * ((m + n + 1).choose m : ℝ) := by
        exact_mod_cast hchooseNat
      apply (mul_left_cancel₀ (show (m + 1 : ℝ) ≠ 0 by positivity))
      calc
        (m + 1 : ℝ) * a (m + 1) n =
            (n + 1 : ℝ) * a m (n + 1) := hxy
        _ = (n + 1 : ℝ) *
            (((m + n + 1).choose m : ℝ) * c (m + n + 1)) := by
              rw [ih (n + 1)]
              simp only [diagonalLift]
              rw [show m + (n + 1) = m + n + 1 by omega]
        _ = (m + 1 : ℝ) *
            (((m + n + 1).choose (m + 1) : ℝ) * c (m + n + 1)) := by
              calc
                (n + 1 : ℝ) *
                    (((m + n + 1).choose m : ℝ) * c (m + n + 1)) =
                    ((n + 1 : ℝ) * ((m + n + 1).choose m : ℝ)) *
                      c (m + n + 1) := by ring
                _ = ((m + 1 : ℝ) *
                    ((m + n + 1).choose (m + 1) : ℝ)) *
                      c (m + n + 1) := by rw [hchoose]
                _ = (m + 1 : ℝ) *
                    (((m + n + 1).choose (m + 1) : ℝ) *
                      c (m + n + 1)) := by ring
        _ = (m + 1 : ℝ) * diagonalLift c (m + 1) n := by
              simp only [diagonalLift]
              rw [show m + 1 + n = m + n + 1 by omega]

/-- Exact binomial product identity for unweighted diagonal lifts. -/
theorem cauchyProduct_diagonalLift (c d : ℕ → ℝ) :
    cauchyProduct (diagonalLift c) (diagonalLift d) =
      diagonalLift (convolution c d) := by
  apply eq_diagonalLift_of_coeffX_eq_coeffY
  · intro n
    simp [convolution, diagonalLift]
  · rw [coeffX_cauchyProduct, coeffY_cauchyProduct,
      coeffX_diagonalLift, coeffX_diagonalLift,
      coeffY_diagonalLift, coeffY_diagonalLift]

/-- Multiplying both variables' coefficients by geometric weights commutes
with bivariate Cauchy products. -/
def coefficientScale (R S : ℝ) (a : Coeff) : Coeff :=
  fun m n => R ^ m * S ^ n * a m n

theorem cauchyProduct_coefficientScale (R S : ℝ) (a b : Coeff) :
    cauchyProduct (coefficientScale R S a) (coefficientScale R S b) =
      coefficientScale R S (cauchyProduct a b) := by
  funext m n
  simp only [cauchyProduct, coefficientScale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro kl hkl
  have hx : ij.1 + ij.2 = m := Finset.mem_antidiagonal.mp hij
  have hy : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
  have hRx : R ^ ij.1 * R ^ ij.2 = R ^ m := by
    rw [← pow_add, hx]
  have hSy : S ^ kl.1 * S ^ kl.2 = S ^ n := by
    rw [← pow_add, hy]
  calc
    R ^ ij.1 * S ^ kl.1 * a ij.1 kl.1 *
        (R ^ ij.2 * S ^ kl.2 * b ij.2 kl.2) =
        (R ^ ij.1 * R ^ ij.2) * (S ^ kl.1 * S ^ kl.2) *
          (a ij.1 kl.1 * b ij.2 kl.2) := by ring
    _ = R ^ m * S ^ n * (a ij.1 kl.1 * b ij.2 kl.2) := by
      rw [hRx, hSy]

theorem coefficientScale_diagonalLift (c : ℕ → ℝ) (R S : ℝ) :
    coefficientScale R S (diagonalLift c) =
      diagonalTransportEnvelope c R S := by
  funext m n
  simp only [coefficientScale, diagonalLift, diagonalTransportEnvelope]
  ring

/-- Exact product identity for the weighted diagonal envelopes. -/
theorem cauchyProduct_diagonalTransportEnvelope
    (c d : ℕ → ℝ) (R S : ℝ) :
    cauchyProduct (diagonalTransportEnvelope c R S)
        (diagonalTransportEnvelope d R S) =
      diagonalConvolution c d R S := by
  rw [← coefficientScale_diagonalLift c R S,
    ← coefficientScale_diagonalLift d R S,
    cauchyProduct_coefficientScale, cauchyProduct_diagonalLift]
  funext m n
  simp only [coefficientScale, diagonalLift, diagonalConvolution]
  ring

/-- Actual bivariate Cauchy products are bounded by the weighted diagonal
convolution of their scalar majorants. -/
theorem abs_cauchyProduct_le_diagonalConvolution
    {a b : Coeff} {c d : ℕ → ℝ} {R S : ℝ}
    (ha : ∀ m n, |a m n| ≤ diagonalTransportEnvelope c R S m n)
    (hb : ∀ m n, |b m n| ≤ diagonalTransportEnvelope d R S m n) :
    ∀ m n, |cauchyProduct a b m n| ≤ diagonalConvolution c d R S m n := by
  intro m n
  calc
    |cauchyProduct a b m n| ≤
        ∑ ij ∈ Finset.antidiagonal m,
          ∑ kl ∈ Finset.antidiagonal n,
            |a ij.1 kl.1 * b ij.2 kl.2| := by
      unfold cauchyProduct
      exact (Finset.abs_sum_le_sum_abs _ _).trans <|
        Finset.sum_le_sum fun ij _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ij ∈ Finset.antidiagonal m,
          ∑ kl ∈ Finset.antidiagonal n,
            diagonalTransportEnvelope c R S ij.1 kl.1 *
              diagonalTransportEnvelope d R S ij.2 kl.2 := by
      apply Finset.sum_le_sum
      intro ij hij
      apply Finset.sum_le_sum
      intro kl hkl
      rw [abs_mul]
      exact mul_le_mul (ha _ _) (hb _ _) (abs_nonneg _)
        ((abs_nonneg _).trans (ha _ _))
    _ = diagonalConvolution c d R S m n := by
      exact congrFun (congrFun (cauchyProduct_diagonalTransportEnvelope c d R S) m) n

/-! ## Evaluation of coefficient products -/

/-- Multiplying the coefficient convolution by `z^n` is the same as taking
the Cauchy convolution of the already weighted terms. -/
theorem convolution_mul_pow (c d : ℕ → ℝ) (z : ℝ) (n : ℕ) :
    convolution c d n * z ^ n =
      ∑ ij ∈ Finset.antidiagonal n,
        (c ij.1 * z ^ ij.1) * (d ij.2 * z ^ ij.2) := by
  unfold convolution
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hadd : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  rw [← hadd, pow_add]
  ring

/-- Absolute summability of two weighted scalar series implies summability of
their weighted Cauchy product. -/
theorem summable_convolution_mul_pow
    {c d : ℕ → ℝ} {z : ℝ}
    (hc : Summable fun n => ‖c n * z ^ n‖)
    (hd : Summable fun n => ‖d n * z ^ n‖) :
    Summable fun n => convolution c d n * z ^ n := by
  have hnorm := summable_norm_sum_mul_antidiagonal_of_summable_norm hc hd
  apply hnorm.of_norm.congr
  intro n
  exact (convolution_mul_pow c d z n).symm

/-- The ordinary one-variable Cauchy product theorem, phrased using the
coefficient convention of this project. -/
theorem tsum_convolution_mul_pow
    {c d : ℕ → ℝ} {z : ℝ}
    (hc : Summable fun n => ‖c n * z ^ n‖)
    (hd : Summable fun n => ‖d n * z ^ n‖) :
    (∑' n, c n * z ^ n) * (∑' n, d n * z ^ n) =
      ∑' n, convolution c d n * z ^ n := by
  calc
    (∑' n, c n * z ^ n) * (∑' n, d n * z ^ n) =
        ∑' n, ∑ ij ∈ Finset.antidiagonal n,
          (c ij.1 * z ^ ij.1) * (d ij.2 * z ^ ij.2) :=
      tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hc hd
    _ = ∑' n, convolution c d n * z ^ n := by
      apply tsum_congr
      intro n
      exact (convolution_mul_pow c d z n).symm

/-- Row evaluation of a bivariate Cauchy product is the finite Cauchy sum of
the evaluated input rows. -/
theorem rowEval_cauchyProduct
    {a b : Coeff} {y : ℝ}
    (ha : ∀ m, Summable fun n => ‖rowTerm a m n y‖)
    (hb : ∀ m, Summable fun n => ‖rowTerm b m n y‖)
    (m : ℕ) :
    rowEval (cauchyProduct a b) m y =
      ∑ ij ∈ Finset.antidiagonal m,
        rowEval a ij.1 y * rowEval b ij.2 y := by
  have hprod (ij : ℕ × ℕ) :
      Summable fun n => convolution (a ij.1) (b ij.2) n * y ^ n := by
    exact summable_convolution_mul_pow (ha ij.1) (hb ij.2)
  unfold rowEval rowTerm
  calc
    ∑' n, cauchyProduct a b m n * y ^ n =
        ∑' n, ∑ ij ∈ Finset.antidiagonal m,
          convolution (a ij.1) (b ij.2) n * y ^ n := by
      apply tsum_congr
      intro n
      unfold cauchyProduct convolution
      rw [Finset.sum_mul]
    _ = ∑ ij ∈ Finset.antidiagonal m,
        ∑' n, convolution (a ij.1) (b ij.2) n * y ^ n := by
      exact Summable.tsum_finsetSum fun ij hij => hprod ij
    _ = ∑ ij ∈ Finset.antidiagonal m,
        (∑' n, a ij.1 n * y ^ n) * (∑' n, b ij.2 n * y ^ n) := by
      apply Finset.sum_congr rfl
      intro ij hij
      exact (tsum_convolution_mul_pow (ha ij.1) (hb ij.2)).symm

/-- Evaluating an absolutely summable bivariate Cauchy product gives the
product of the two evaluations. -/
theorem eval_cauchyProduct
    {a b : Coeff} {rx ry x y : ℝ}
    (ha : SummableOnBox a rx ry) (hb : SummableOnBox b rx ry)
    (hx : |x| ≤ rx) (hy : |y| ≤ ry) :
    eval (cauchyProduct a b) x y = eval a x y * eval b x y := by
  have haRow : ∀ m, Summable fun n => ‖rowTerm a m n y‖ := by
    intro m
    exact (ha.row m).of_norm_bounded fun n => by
      rw [norm_norm]
      exact norm_rowTerm_le a m n hy
  have hbRow : ∀ m, Summable fun n => ‖rowTerm b m n y‖ := by
    intro m
    exact (hb.row m).of_norm_bounded fun n => by
      rw [norm_norm]
      exact norm_rowTerm_le b m n hy
  have haOuter : Summable fun m => ‖rowEval a m y * x ^ m‖ :=
    ha.outer.of_norm_bounded fun m => by
      rw [norm_norm]
      exact ha.norm_rowEval_mul_pow_le hx hy m
  have hbOuter : Summable fun m => ‖rowEval b m y * x ^ m‖ :=
    hb.outer.of_norm_bounded fun m => by
      rw [norm_norm]
      exact hb.norm_rowEval_mul_pow_le hx hy m
  unfold eval
  calc
    ∑' m, rowEval (cauchyProduct a b) m y * x ^ m =
        ∑' m, (∑ ij ∈ Finset.antidiagonal m,
          rowEval a ij.1 y * rowEval b ij.2 y) * x ^ m := by
      apply tsum_congr
      intro m
      rw [rowEval_cauchyProduct haRow hbRow]
    _ = ∑' m, ∑ ij ∈ Finset.antidiagonal m,
        (rowEval a ij.1 y * x ^ ij.1) *
          (rowEval b ij.2 y * x ^ ij.2) := by
      apply tsum_congr
      intro m
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ij hij
      have hadd : ij.1 + ij.2 = m := Finset.mem_antidiagonal.mp hij
      rw [← hadd, pow_add]
      ring
    _ = (∑' m, rowEval a m y * x ^ m) *
        (∑' m, rowEval b m y * x ^ m) :=
      (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
        haOuter hbOuter).symm

/-! ## Finite-dimensional sums and operator application -/

/-- Coefficient arrays with values in a finite-dimensional coordinate
space.  The norm is Mathlib's supremum norm on the finite function type. -/
abbrev VectorCoeff (ι : Type*) := ℕ → ℕ → (ι → ℝ)

/-- Coefficient arrays of coordinate matrices. -/
abbrev MatrixCoeff (ι κ : Type*) := ℕ → ℕ → (ι → κ → ℝ)

/-- Coefficients of the concrete two-component reduced state. -/
abbrev FirstOrderStateCoeff := ℕ → ℕ → FirstOrderState

/-- Coefficients of the concrete two-by-two reduced operator. -/
abbrev FirstOrderOperatorCoeff := ℕ → ℕ → FirstOrderOperator

/-- Supremum-norm estimate for a finite coordinate matrix acting on a
finite coordinate vector. -/
theorem norm_matrix_mulVec_le_card
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → κ → ℝ) (v : κ → ℝ) :
    ‖Matrix.mulVec A v‖ ≤ (Fintype.card κ : ℝ) * ‖A‖ * ‖v‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  change |∑ j, A i j * v j| ≤ _
  calc
    |∑ j, A i j * v j| ≤ ∑ j, |A i j * v j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : κ, ‖A‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      apply mul_le_mul
      · calc
          |A i j| ≤ ‖A i‖ := by
            simpa only [Real.norm_eq_abs] using norm_le_pi_norm (A i) j
          _ ≤ ‖A‖ := norm_le_pi_norm A i
      · simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j
      · exact abs_nonneg _
      · exact norm_nonneg _
    _ = (Fintype.card κ : ℝ) * ‖A‖ * ‖v‖ := by
      simp [nsmul_eq_mul]
      ring

/-- The concrete operator norm constant for the reduced two-component
system. -/
theorem norm_firstOrderOperator_mulVec_le
    (A : FirstOrderOperator) (v : FirstOrderState) :
    ‖Matrix.mulVec A v‖ ≤ 2 * ‖A‖ * ‖v‖ := by
  simpa using norm_matrix_mulVec_le_card A v

/-- Finite sums preserve diagonal envelopes, with the scalar amplitudes
summed coefficientwise. -/
theorem norm_finsetSum_le_diagonalTransportEnvelope
    {E ι : Type*} [SeminormedAddCommGroup E]
    {s : Finset ι} {a : ι → ℕ → ℕ → E} {c : ι → ℕ → ℝ}
    {R S : ℝ}
    (ha : ∀ i ∈ s, ∀ m n,
      ‖a i m n‖ ≤ diagonalTransportEnvelope (c i) R S m n) :
    ∀ m n, ‖∑ i ∈ s, a i m n‖ ≤
      diagonalTransportEnvelope (fun k => ∑ i ∈ s, c i k) R S m n := by
  intro m n
  calc
    ‖∑ i ∈ s, a i m n‖ ≤ ∑ i ∈ s, ‖a i m n‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, diagonalTransportEnvelope (c i) R S m n := by
      exact Finset.sum_le_sum fun i hi => ha i hi m n
    _ = diagonalTransportEnvelope (fun k => ∑ i ∈ s, c i k) R S m n := by
      simp only [diagonalTransportEnvelope]
      rw [Finset.mul_sum]

/-- The bivariate coefficient product for a matrix-valued series applied to
a vector-valued series, including the finite coordinate contraction. -/
def matrixVectorCauchyProduct
    {ι κ : Type*} [Fintype κ]
    (A : MatrixCoeff ι κ) (v : VectorCoeff κ) : VectorCoeff ι :=
  fun m n i =>
    ∑ j, cauchyProduct (fun p q => A p q i j) (fun p q => v p q j) m n

/-- Supremum-norm bounds for coefficient matrices and vectors yield the
expected diagonal-convolution bound for matrix-vector application.  The
factor `card κ` is the explicit cost of the coordinate contraction. -/
theorem norm_matrixVectorCauchyProduct_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : MatrixCoeff ι κ} {v : VectorCoeff κ}
    {c d : ℕ → ℝ} {R S : ℝ}
    (hc : ∀ k, 0 ≤ c k) (hd : ∀ k, 0 ≤ d k)
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hA : ∀ m n, ‖A m n‖ ≤ diagonalTransportEnvelope c R S m n)
    (hv : ∀ m n, ‖v m n‖ ≤ diagonalTransportEnvelope d R S m n) :
    ∀ m n, ‖matrixVectorCauchyProduct A v m n‖ ≤
      (Fintype.card κ : ℝ) * diagonalConvolution c d R S m n := by
  intro m n
  have hdiag : 0 ≤ diagonalConvolution c d R S m n := by
    unfold diagonalConvolution
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hR _))
        (pow_nonneg hS _))
      (convolution_nonneg hc hd (m + n))
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hdiag)]
  intro i
  change ‖∑ j, cauchyProduct (fun p q => A p q i j)
      (fun p q => v p q j) m n‖ ≤ _
  calc
    ‖∑ j, cauchyProduct (fun p q => A p q i j)
        (fun p q => v p q j) m n‖ ≤
        ∑ j, |cauchyProduct (fun p q => A p q i j)
          (fun p q => v p q j) m n| := norm_sum_le _ _
    _ ≤ ∑ _j : κ, diagonalConvolution c d R S m n := by
      apply Finset.sum_le_sum
      intro j hj
      apply abs_cauchyProduct_le_diagonalConvolution
      · intro p q
        calc
          |A p q i j| ≤ ‖A p q i‖ := by
            simpa only [Real.norm_eq_abs] using norm_le_pi_norm (A p q i) j
          _ ≤ ‖A p q‖ := norm_le_pi_norm _ i
          _ ≤ diagonalTransportEnvelope c R S p q := hA p q
      · intro p q
        calc
          |v p q j| ≤ ‖v p q‖ := by
            simpa only [Real.norm_eq_abs] using norm_le_pi_norm (v p q) j
          _ ≤ diagonalTransportEnvelope d R S p q := hv p q
    _ = (Fintype.card κ : ℝ) * diagonalConvolution c d R S m n := by
      simp [nsmul_eq_mul]

/-- The coefficientwise matrix-action estimate specialized to the reduced
two-component state.  Its exact contraction cost is `2`. -/
theorem norm_firstOrder_matrixVectorCauchyProduct_le
    {A : FirstOrderOperatorCoeff} {v : FirstOrderStateCoeff}
    {c d : ℕ → ℝ} {R S : ℝ}
    (hc : ∀ k, 0 ≤ c k) (hd : ∀ k, 0 ≤ d k)
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hA : ∀ m n, ‖A m n‖ ≤ diagonalTransportEnvelope c R S m n)
    (hv : ∀ m n, ‖v m n‖ ≤ diagonalTransportEnvelope d R S m n) :
    ∀ m n, ‖matrixVectorCauchyProduct A v m n‖ ≤
      2 * diagonalConvolution c d R S m n := by
  simpa using norm_matrixVectorCauchyProduct_le hc hd hR hS hA hv

/-! ## Recurrence interface for a finite-dimensional reduced system -/

/-- Once the norm coefficients of a finite-dimensional reduced state satisfy
the scalar Catalan/Fuchsian recurrence, every state coefficient obeys the
same explicit diagonal envelope.  This is the direct interface consumed by
the reduced two-component stress-tensor system. -/
theorem norm_le_catalanTransportEnvelope_of_reduced_recurrence
    {ι : Type*} [Fintype ι]
    {a : VectorCoeff ι} {u f : Coeff} {K L M G Q R S : ℝ}
    (ha : ∀ m n, ‖a m n‖ ≤ u m n)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hlinear : L ≤ R * K * Q)
    (hquadratic : M + G ≤ R * Q)
    (hzero : ∀ n, u 0 n ≤ S ^ n * catalanEnvelope K Q n)
    (hfbound : ∀ m n,
      f m n ≤ G * diagonalConvolution (catalanEnvelope K Q)
        (catalanEnvelope K Q) R S m n)
    (hsucc : ∀ m n,
      u (m + 1) n ≤
        (L * (n : ℝ) * u m n +
          M * diagonalConvolution (catalanEnvelope K Q)
            (catalanEnvelope K Q) R S m n + f m n) /
              (m + 1 : ℝ)) :
    ∀ m n, ‖a m n‖ ≤
      diagonalTransportEnvelope (catalanEnvelope K Q) R S m n := by
  intro m n
  exact (ha m n).trans <|
    le_catalanTransportEnvelope_of_quadratic_recurrence
      hK hL hQ hR hS hlinear hquadratic hzero hfbound hsucc m n

/-- Componentwise product-geometric convergence follows from the same
reduced-system recurrence certificate. -/
theorem component_geometricBound_of_reduced_recurrence
    {ι : Type*} [Fintype ι]
    {a : VectorCoeff ι} {u f : Coeff} {K L M G Q R S : ℝ}
    (ha : ∀ m n, ‖a m n‖ ≤ u m n)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hlinear : L ≤ R * K * Q)
    (hquadratic : M + G ≤ R * Q)
    (hzero : ∀ n, u 0 n ≤ S ^ n * catalanEnvelope K Q n)
    (hfbound : ∀ m n,
      f m n ≤ G * diagonalConvolution (catalanEnvelope K Q)
        (catalanEnvelope K Q) R S m n)
    (hsucc : ∀ m n,
      u (m + 1) n ≤
        (L * (n : ℝ) * u m n +
          M * diagonalConvolution (catalanEnvelope K Q)
            (catalanEnvelope K Q) R S m n + f m n) /
              (m + 1 : ℝ)) :
    ∀ i, GeometricBound (fun m n => a m n i) K
      (8 * (K * Q) * R) (8 * (K * Q) * S) := by
  intro i
  refine geometricBound_of_catalan_transport_recurrence
    (a := fun m n => a m n i) (u := u) (f := f) ?_
      hK hL hQ hR hS hlinear hquadratic hzero hfbound hsucc
  intro m n
  calc
    |a m n i| ≤ ‖a m n‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (a m n) i
    _ ≤ u m n := ha m n

/-- Exact vector recurrence interface for the reduced first-order system.

`transport` is the coefficient contribution of the principal Euler term and
`nonlinear` contains the coefficient convolutions from the variable analytic
matrix and source.  The preceding Cauchy-product and matrix-vector theorems
are designed to discharge `hnonlinear`; this theorem then converts the exact
vector equality into the scalar Catalan recurrence without losing the
division by `m+1`. -/
theorem component_geometricBound_of_reduced_vector_recurrence
    {ι : Type*} [Fintype ι]
    {a transport nonlinear : VectorCoeff ι} {f : Coeff}
    {K L M G Q R S : ℝ}
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hlinear : L ≤ R * K * Q)
    (hquadratic : M + G ≤ R * Q)
    (hzero : ∀ n, ‖a 0 n‖ ≤ S ^ n * catalanEnvelope K Q n)
    (hfbound : ∀ m n,
      f m n ≤ G * diagonalConvolution (catalanEnvelope K Q)
        (catalanEnvelope K Q) R S m n)
    (htransport : ∀ m n,
      ‖transport m n‖ ≤ L * ‖a m n‖)
    (hnonlinear : ∀ m n,
      ‖nonlinear m n‖ ≤
        M * diagonalConvolution (catalanEnvelope K Q)
          (catalanEnvelope K Q) R S m n + f m n)
    (hrec : ∀ (m n : ℕ),
      ((m + 1 : ℕ) : ℝ) • a (m + 1) n =
        (n : ℝ) • transport m n + nonlinear m n) :
    ∀ i, GeometricBound (fun m n => a m n i) K
      (8 * (K * Q) * R) (8 * (K * Q) * S) := by
  apply component_geometricBound_of_reduced_recurrence
    (a := a) (u := fun m n => ‖a m n‖) (f := f)
    (fun _ _ => le_rfl) hK hL hQ hR hS hlinear hquadratic hzero hfbound
  intro m n
  have hm : 0 < (m + 1 : ℝ) := by positivity
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hrec' := hrec m n
  push_cast at hrec'
  have hscaled :
      (m + 1 : ℝ) * ‖a (m + 1) n‖ ≤
        L * (n : ℝ) * ‖a m n‖ +
          M * diagonalConvolution (catalanEnvelope K Q)
            (catalanEnvelope K Q) R S m n + f m n := by
    calc
      (m + 1 : ℝ) * ‖a (m + 1) n‖ =
          ‖(m + 1 : ℝ) • a (m + 1) n‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hm]
      _ = ‖(n : ℝ) • transport m n + nonlinear m n‖ := by
        rw [hrec']
      _ ≤ ‖(n : ℝ) • transport m n‖ + ‖nonlinear m n‖ :=
        norm_add_le _ _
      _ = (n : ℝ) * ‖transport m n‖ + ‖nonlinear m n‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hn]
      _ ≤ (n : ℝ) * (L * ‖a m n‖) +
          (M * diagonalConvolution (catalanEnvelope K Q)
            (catalanEnvelope K Q) R S m n + f m n) :=
        add_le_add (mul_le_mul_of_nonneg_left (htransport m n) hn)
          (hnonlinear m n)
      _ = L * (n : ℝ) * ‖a m n‖ +
          M * diagonalConvolution (catalanEnvelope K Q)
            (catalanEnvelope K Q) R S m n + f m n := by ring
  rw [le_div_iff₀ hm]
  nlinarith

end

end CKBivariateConvolutionMajorant

end StressTensor
