import StressTensor.CKGeometricMajorant
import StressTensor.CKSeriesBridge
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Nat.Choose.Central

/-!
# Diagonal and Catalan majorants for the CK recursion

For a bivariate series, the standard CK comparison replaces both variables
by one nonnegative variable `t`.  The coefficient of `x^m y^n` in `B(x+y)`
is `choose (m+n) m * b (m+n)`.  This file formalizes that comparison and
shows that any geometrically bounded diagonal majorant gives exactly the
product-geometric certificate used by `CKGeometricMajorant`.

The second part records the elementary Catalan majorant for a quadratic
coefficient recurrence.  This is the scalar convergence engine used after
the shifted factors `y * Gamma₂` and `y²` have removed the apparent
highest-derivative loss.
-/

namespace StressTensor

namespace CKDiagonalMajorant

open CKPowerSeries CKSeriesBridge CKGeometricMajorant

noncomputable section

/-- The bivariate coefficients of the diagonal substitution `B(x+y)`. -/
def diagonalLift (b : ℕ → ℝ) : Coeff :=
  fun m n => ((m + n).choose m : ℝ) * b (m + n)

/-- Coefficientwise domination by a one-variable diagonal majorant. -/
def IsDiagonalMajorant (a : Coeff) (b : ℕ → ℝ) : Prop :=
  ∀ m n, |a m n| ≤ diagonalLift b m n

/-! ## Integration and the diagonal substitution -/

/-- Formal integration in the `x` variable with zero integration constant. -/
def integrateX (a : Coeff) : Coeff
  | 0, _ => 0
  | m + 1, n => a m n / (m + 1 : ℝ)

/-- Formal integration in the `y` variable with zero integration constant. -/
def integrateY (a : Coeff) : Coeff
  | _, 0 => 0
  | m, n + 1 => a m n / (n + 1 : ℝ)

/-- Two formal integrations in the `x` variable.  This is the right inverse
of `coeffXX` with both Cauchy rows set to zero. -/
def integrateXX (a : Coeff) : Coeff :=
  integrateX (integrateX a)

/-- Formal integration of a scalar coefficient sequence with zero constant. -/
def integrateScalar (b : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => b k / (k + 1 : ℝ)

/-- Formal derivative of a scalar coefficient sequence. -/
def derivativeScalar (b : ℕ → ℝ) (k : ℕ) : ℝ :=
  (k + 1 : ℝ) * b (k + 1)

/-- The binomial identity behind the fact that diagonal comparison is
preserved by integration in either original variable. -/
theorem choose_succ_ratio_identity (m n : ℕ) :
    ((m + n + 1).choose (m + 1) : ℝ) / (m + n + 1 : ℝ) =
      ((m + n).choose m : ℝ) / (m + 1 : ℝ) := by
  have hnat :
      (m + 1) * (m + n + 1).choose (m + 1) =
        (m + n + 1) * (m + n).choose m := by
    calc
      (m + 1) * (m + n + 1).choose (m + 1) =
          (m + n + 1).choose (m + 1) * (m + 1) := Nat.mul_comm _ _
      _ = (m + n + 1).choose m * (n + 1) := by
        rw [Nat.choose_succ_right_eq]
        congr 1
        omega
      _ = (m + n).choose m * (m + n + 1) := by
        rw [Nat.choose_mul_succ_eq]
        congr 1
        omega
      _ = (m + n + 1) * (m + n).choose m := Nat.mul_comm _ _
  have hreal :
      (m + 1 : ℝ) * ((m + n + 1).choose (m + 1) : ℝ) =
        (m + n + 1 : ℝ) * ((m + n).choose m : ℝ) := by
    exact_mod_cast hnat
  field_simp
  nlinarith

/-- Integrating a nonnegative scalar majorant preserves nonnegativity. -/
theorem integrateScalar_nonneg {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k) :
    ∀ k, 0 ≤ integrateScalar b k := by
  intro k
  cases k with
  | zero => simp [integrateScalar]
  | succ k =>
      exact div_nonneg (hb k) (by positivity)

/-- Zero-constant integration in `x` preserves a diagonal majorant.  At
positive `x` degree the comparison is an equality; at degree zero it is the
obvious inequality `0 ≤ diagonalLift (integrateScalar b) 0 n`. -/
theorem IsDiagonalMajorant.integrateX
    {a : Coeff} {b : ℕ → ℝ}
    (h : IsDiagonalMajorant a b) (hb : ∀ k, 0 ≤ b k) :
    IsDiagonalMajorant (integrateX a) (integrateScalar b) := by
  intro m n
  cases m with
  | zero =>
      rw [show CKDiagonalMajorant.integrateX a 0 n = 0 by rfl]
      simp only [abs_zero]
      simpa [diagonalLift] using integrateScalar_nonneg hb n
  | succ m =>
      change |a m n / (m + 1 : ℝ)| ≤
        ((m + 1 + n).choose (m + 1) : ℝ) * integrateScalar b (m + 1 + n)
      rw [show m + 1 + n = m + n + 1 by omega]
      simp only [integrateScalar]
      push_cast
      rw [abs_div]
      have hden : 0 < (m + 1 : ℝ) := by positivity
      have hchoose := choose_succ_ratio_identity m n
      calc
        |a m n| / |(m + 1 : ℝ)|
            ≤ (((m + n).choose m : ℝ) * b (m + n)) / (m + 1 : ℝ) := by
              rw [abs_of_pos hden]
              exact div_le_div_of_nonneg_right (h m n) hden.le
        _ = (((m + n).choose m : ℝ) / (m + 1 : ℝ)) * b (m + n) := by
              ring
        _ = (((m + n + 1).choose (m + 1) : ℝ) / (m + n + 1 : ℝ)) *
              b (m + n) := by rw [hchoose]
        _ = ((m + n + 1).choose (m + 1) : ℝ) *
              (b (m + n) / (m + n + 1 : ℝ)) := by ring

/-- Zero-constant integration in `y` preserves the same scalar diagonal
majorant. -/
theorem IsDiagonalMajorant.integrateY
    {a : Coeff} {b : ℕ → ℝ}
    (h : IsDiagonalMajorant a b) (hb : ∀ k, 0 ≤ b k) :
    IsDiagonalMajorant (integrateY a) (integrateScalar b) := by
  intro m n
  cases n with
  | zero =>
      rw [show CKDiagonalMajorant.integrateY a m 0 = 0 by rfl]
      simp only [abs_zero]
      simpa [diagonalLift] using integrateScalar_nonneg hb m
  | succ n =>
      change |a m n / (n + 1 : ℝ)| ≤
        ((m + (n + 1)).choose m : ℝ) * integrateScalar b (m + (n + 1))
      rw [show m + (n + 1) = m + n + 1 by omega]
      simp only [integrateScalar]
      push_cast
      rw [abs_div]
      have hden : 0 < (n + 1 : ℝ) := by positivity
      have hchoose :
          ((m + n + 1).choose m : ℝ) / (m + n + 1 : ℝ) =
            ((m + n).choose m : ℝ) / (n + 1 : ℝ) := by
        have htop :
            (m + n + 1).choose m = (n + m + 1).choose (n + 1) := by
          calc
            (m + n + 1).choose m = (m + (n + 1)).choose m := by
              rw [show m + n + 1 = m + (n + 1) by omega]
            _ = (m + (n + 1)).choose (n + 1) := Nat.choose_symm_add
            _ = (n + m + 1).choose (n + 1) := by
              rw [show m + (n + 1) = n + m + 1 by omega]
        have hbot : (m + n).choose m = (n + m).choose n := by
          calc
            (m + n).choose m = (m + n).choose n := Nat.choose_symm_add
            _ = (n + m).choose n := by rw [add_comm]
        rw [htop, hbot]
        simpa [add_comm, add_left_comm, add_assoc] using
          choose_succ_ratio_identity n m
      calc
        |a m n| / |(n + 1 : ℝ)|
            ≤ (((m + n).choose m : ℝ) * b (m + n)) / (n + 1 : ℝ) := by
              rw [abs_of_pos hden]
              exact div_le_div_of_nonneg_right (h m n) hden.le
        _ = (((m + n).choose m : ℝ) / (n + 1 : ℝ)) * b (m + n) := by
              ring
        _ = (((m + n + 1).choose m : ℝ) / (m + n + 1 : ℝ)) *
              b (m + n) := by rw [hchoose]
        _ = ((m + n + 1).choose m : ℝ) *
              (b (m + n) / (m + n + 1 : ℝ)) := by ring

/-- Two `x` integrations preserve diagonal comparison. -/
theorem IsDiagonalMajorant.integrateXX
    {a : Coeff} {b : ℕ → ℝ}
    (h : IsDiagonalMajorant a b) (hb : ∀ k, 0 ≤ b k) :
    IsDiagonalMajorant (integrateXX a)
      (integrateScalar (integrateScalar b)) := by
  exact (h.integrateX hb).integrateX (integrateScalar_nonneg hb)

/-- Double `x` integration has zero zeroth Cauchy row. -/
@[simp] theorem integrateXX_row_zero (a : Coeff) (n : ℕ) :
    integrateXX a 0 n = 0 := by
  rfl

/-- Double `x` integration has zero first Cauchy row. -/
@[simp] theorem integrateXX_row_one (a : Coeff) (n : ℕ) :
    integrateXX a 1 n = 0 := by
  simp [integrateXX, CKDiagonalMajorant.integrateX]

/-- `coeffXX` is a left inverse of double zero-constant integration. -/
@[simp] theorem coeffXX_integrateXX (a : Coeff) :
    CKSeriesBridge.coeffXX (integrateXX a) = a := by
  funext m n
  simp only [CKSeriesBridge.coeffXX]
  have hint : integrateXX a (m + 2) n =
      (a m n / (m + 1 : ℝ)) / (m + 2 : ℝ) := by
    simp [integrateXX, CKDiagonalMajorant.integrateX]
    rw [show (m : ℝ) + 1 + 1 = (m + 2 : ℕ) by push_cast; ring]
    push_cast
    rfl
  rw [hint]
  have hm1 : (m + 1 : ℝ) ≠ 0 := by positivity
  have hm2 : (m + 2 : ℝ) ≠ 0 := by positivity
  field_simp

/-! Differentiation has an exact diagonal comparison: both original
variables become the same scalar variable after the substitution `t=x+y`. -/

/-- The binomial identity for differentiating the `x` part of `(x+y)^(m+n+1)`. -/
theorem succ_mul_choose_succ_left (m n : ℕ) :
    (m + 1) * (m + n + 1).choose (m + 1) =
      (m + n + 1) * (m + n).choose m := by
  calc
    (m + 1) * (m + n + 1).choose (m + 1) =
        (m + n + 1).choose (m + 1) * (m + 1) := Nat.mul_comm _ _
    _ = (m + n + 1).choose m * (n + 1) := by
      rw [Nat.choose_succ_right_eq]
      congr 1
      omega
    _ = (m + n).choose m * (m + n + 1) := by
      rw [Nat.choose_mul_succ_eq]
      congr 1
      omega
    _ = (m + n + 1) * (m + n).choose m := Nat.mul_comm _ _

/-- The analogous binomial identity for the `y` derivative. -/
theorem succ_mul_choose_succ_right (m n : ℕ) :
    (n + 1) * (m + n + 1).choose m =
      (m + n + 1) * (m + n).choose m := by
  calc
    (n + 1) * (m + n + 1).choose m =
        (m + n + 1).choose m * (n + 1) := Nat.mul_comm _ _
    _ = (m + n).choose m * (m + n + 1) := by
      rw [Nat.choose_mul_succ_eq]
      congr 1
      omega
    _ = (m + n + 1) * (m + n).choose m := Nat.mul_comm _ _

/-- Differentiating a diagonal lift in `x` is exactly scalar
differentiation followed by diagonal lifting. -/
theorem coeffX_diagonalLift (b : ℕ → ℝ) :
    coeffX (diagonalLift b) = diagonalLift (derivativeScalar b) := by
  funext m n
  simp only [coeffX, diagonalLift, derivativeScalar]
  have hnat := succ_mul_choose_succ_left m n
  have hreal :
      (m + 1 : ℝ) * ((m + n + 1).choose (m + 1) : ℝ) =
        (m + n + 1 : ℝ) * ((m + n).choose m : ℝ) := by
    exact_mod_cast hnat
  rw [show m + 1 + n = m + n + 1 by omega]
  push_cast
  calc
    (m + 1 : ℝ) *
        (((m + n + 1).choose (m + 1) : ℝ) * b (m + n + 1)) =
        ((m + 1 : ℝ) * ((m + n + 1).choose (m + 1) : ℝ)) *
          b (m + n + 1) := by ring
    _ = ((m + n + 1 : ℝ) * ((m + n).choose m : ℝ)) *
          b (m + n + 1) := by rw [hreal]
    _ = ((m + n).choose m : ℝ) *
          ((m + n + 1 : ℝ) * b (m + n + 1)) := by ring

/-- Differentiating a diagonal lift in `y` is exactly scalar
differentiation followed by diagonal lifting. -/
theorem coeffY_diagonalLift (b : ℕ → ℝ) :
    coeffY (diagonalLift b) = diagonalLift (derivativeScalar b) := by
  funext m n
  simp only [coeffY, diagonalLift, derivativeScalar]
  have hnat := succ_mul_choose_succ_right m n
  have hreal :
      (n + 1 : ℝ) * ((m + n + 1).choose m : ℝ) =
        (m + n + 1 : ℝ) * ((m + n).choose m : ℝ) := by
    exact_mod_cast hnat
  rw [show m + (n + 1) = m + n + 1 by omega]
  push_cast
  calc
    (n + 1 : ℝ) *
        (((m + n + 1).choose m : ℝ) * b (m + n + 1)) =
        ((n + 1 : ℝ) * ((m + n + 1).choose m : ℝ)) *
          b (m + n + 1) := by ring
    _ = ((m + n + 1 : ℝ) * ((m + n).choose m : ℝ)) *
          b (m + n + 1) := by rw [hreal]
    _ = ((m + n).choose m : ℝ) *
          ((m + n + 1 : ℝ) * b (m + n + 1)) := by ring

/-- Scalar coefficient differentiation preserves nonnegativity. -/
theorem derivativeScalar_nonneg {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k) :
    ∀ k, 0 ≤ derivativeScalar b k := by
  intro k
  exact mul_nonneg (by positivity) (hb (k + 1))

/-- A diagonal majorant differentiates in `x` without any extra loss beyond
the ordinary scalar derivative. -/
theorem IsDiagonalMajorant.coeffX
    {a : Coeff} {b : ℕ → ℝ}
    (h : IsDiagonalMajorant a b) :
    IsDiagonalMajorant (CKSeriesBridge.coeffX a) (derivativeScalar b) := by
  intro m n
  rw [← coeffX_diagonalLift]
  simp only [CKSeriesBridge.coeffX, abs_mul]
  have hm : 0 ≤ (m + 1 : ℝ) := by positivity
  rw [abs_of_nonneg hm]
  exact mul_le_mul_of_nonneg_left (h (m + 1) n) hm

/-- The same exact majorant rule for differentiation in `y`. -/
theorem IsDiagonalMajorant.coeffY
    {a : Coeff} {b : ℕ → ℝ}
    (h : IsDiagonalMajorant a b) :
    IsDiagonalMajorant (CKSeriesBridge.coeffY a) (derivativeScalar b) := by
  intro m n
  rw [← coeffY_diagonalLift]
  simp only [CKSeriesBridge.coeffY, abs_mul]
  have hn : 0 ≤ (n + 1 : ℝ) := by positivity
  rw [abs_of_nonneg hn]
  exact mul_le_mul_of_nonneg_left (h m (n + 1)) hn

/-- The coefficient implementation of `xx` agrees with two successive
applications of the first-derivative implementation. -/
theorem coeffXX_eq_coeffX_coeffX (a : Coeff) :
    CKSeriesBridge.coeffXX a =
      CKSeriesBridge.coeffX (CKSeriesBridge.coeffX a) := by
  funext m n
  simp only [CKSeriesBridge.coeffXX, CKSeriesBridge.coeffX]
  push_cast
  ring

/-- The coefficient implementation of `xy` agrees with successive first
derivatives. -/
theorem coeffXY_eq_coeffX_coeffY (a : Coeff) :
    CKSeriesBridge.coeffXY a =
      CKSeriesBridge.coeffX (CKSeriesBridge.coeffY a) := by
  funext m n
  simp only [CKSeriesBridge.coeffXY, CKSeriesBridge.coeffX,
    CKSeriesBridge.coeffY]
  ring

/-- The coefficient implementation of `yy` agrees with two successive
applications of the first-derivative implementation. -/
theorem coeffYY_eq_coeffY_coeffY (a : Coeff) :
    CKSeriesBridge.coeffYY a =
      CKSeriesBridge.coeffY (CKSeriesBridge.coeffY a) := by
  funext m n
  simp only [CKSeriesBridge.coeffYY, CKSeriesBridge.coeffY]
  push_cast
  ring

/-- Second `x` derivatives are controlled by the second scalar derivative. -/
theorem IsDiagonalMajorant.coeffXX
    {a : Coeff} {b : ℕ → ℝ}
    (h : IsDiagonalMajorant a b) :
    IsDiagonalMajorant (CKSeriesBridge.coeffXX a)
      (derivativeScalar (derivativeScalar b)) := by
  rw [coeffXX_eq_coeffX_coeffX]
  exact h.coeffX.coeffX

/-- Mixed derivatives are controlled by the second scalar derivative. -/
theorem IsDiagonalMajorant.coeffXY
    {a : Coeff} {b : ℕ → ℝ}
    (h : IsDiagonalMajorant a b) :
    IsDiagonalMajorant (CKSeriesBridge.coeffXY a)
      (derivativeScalar (derivativeScalar b)) := by
  rw [coeffXY_eq_coeffX_coeffY]
  exact h.coeffY.coeffX

/-- Second `y` derivatives are controlled by the second scalar derivative. -/
theorem IsDiagonalMajorant.coeffYY
    {a : Coeff} {b : ℕ → ℝ}
    (h : IsDiagonalMajorant a b) :
    IsDiagonalMajorant (CKSeriesBridge.coeffYY a)
      (derivativeScalar (derivativeScalar b)) := by
  rw [coeffYY_eq_coeffY_coeffY]
  exact h.coeffY.coeffY

/-- Every binomial coefficient is bounded by the corresponding power of two. -/
theorem choose_cast_le_two_pow (m n : ℕ) :
    ((m + n).choose m : ℝ) ≤ (2 : ℝ) ^ (m + n) := by
  exact_mod_cast Nat.choose_le_two_pow (m + n) m

/-- A geometric bound for the scalar diagonal majorant becomes a separable
geometric bound for the bivariate coefficients.  The factor two in each
variable is the cost of `choose (m+n) m ≤ 2^(m+n)`. -/
theorem IsDiagonalMajorant.geometricBound
    {a : Coeff} {b : ℕ → ℝ} {M s : ℝ}
    (h : IsDiagonalMajorant a b) (hM : 0 ≤ M) (hs : 0 ≤ s)
    (hb : ∀ k, b k ≤ M * s ^ k) :
    GeometricBound a M (2 * s) (2 * s) := by
  refine ⟨hM, mul_nonneg (by norm_num) hs, mul_nonneg (by norm_num) hs, ?_⟩
  intro m n
  calc
    |a m n| ≤ ((m + n).choose m : ℝ) * b (m + n) := h m n
    _ ≤ ((m + n).choose m : ℝ) * (M * s ^ (m + n)) := by
      exact mul_le_mul_of_nonneg_left (hb (m + n)) (Nat.cast_nonneg _)
    _ ≤ (2 : ℝ) ^ (m + n) * (M * s ^ (m + n)) := by
      exact mul_le_mul_of_nonneg_right (choose_cast_le_two_pow m n)
        (mul_nonneg hM (pow_nonneg hs _))
    _ = M * (2 * s) ^ m * (2 * s) ^ n := by
      rw [pow_add, pow_add]
      ring

/-! ## The scalar Catalan envelope -/

/-- Cauchy convolution of two scalar coefficient sequences. -/
def convolution (u v : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ ij ∈ Finset.antidiagonal n, u ij.1 * v ij.2

/-- The scaled Catalan sequence solving `e₀ = K` and
`e_(n+1) = L * ∑_(i+j=n) e_i e_j`. -/
def catalanEnvelope (K L : ℝ) (n : ℕ) : ℝ :=
  K * (K * L) ^ n * (catalan n : ℝ)

@[simp] theorem catalanEnvelope_zero (K L : ℝ) :
    catalanEnvelope K L 0 = K := by
  simp [catalanEnvelope, catalan_zero]

/-- The Catalan envelope has the exact quadratic convolution recurrence. -/
theorem catalanEnvelope_succ (K L : ℝ) (n : ℕ) :
    catalanEnvelope K L (n + 1) =
      L * convolution (catalanEnvelope K L) (catalanEnvelope K L) n := by
  simp only [catalanEnvelope, convolution, pow_succ]
  rw [catalan_succ']
  push_cast
  rw [Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have hadd : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  rw [← hadd, pow_add]
  ring

/-- Catalan numbers have the elementary geometric bound `Cₙ ≤ 4ⁿ`. -/
theorem catalan_cast_le_four_pow (n : ℕ) :
    (catalan n : ℝ) ≤ (4 : ℝ) ^ n := by
  exact_mod_cast
    (calc
      catalan n = n.centralBinom / (n + 1) := catalan_eq_centralBinom_div n
      _ ≤ n.centralBinom := Nat.div_le_self _ _
      _ ≤ 4 ^ n := Nat.centralBinom_le_four_pow n)

/-- The scaled Catalan envelope is geometrically bounded. -/
theorem catalanEnvelope_le_geometric
    {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (n : ℕ) :
    catalanEnvelope K L n ≤ K * (4 * (K * L)) ^ n := by
  calc
    catalanEnvelope K L n =
        K * (K * L) ^ n * (catalan n : ℝ) := rfl
    _ ≤ K * (K * L) ^ n * (4 : ℝ) ^ n := by
      exact mul_le_mul_of_nonneg_left (catalan_cast_le_four_pow n)
        (mul_nonneg hK (pow_nonneg (mul_nonneg hK hL) _))
    _ = K * (4 * (K * L)) ^ n := by
      rw [mul_pow]
      ring

/-- Positivity of every Catalan-envelope coefficient. -/
theorem catalanEnvelope_nonneg
    {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (n : ℕ) :
    0 ≤ catalanEnvelope K L n := by
  unfold catalanEnvelope
  exact mul_nonneg (mul_nonneg hK (pow_nonneg (mul_nonneg hK hL) _))
    (Nat.cast_nonneg _)

/-- A nonnegative scalar sequence satisfying a quadratic convolution
inequality is dominated coefficientwise by the corresponding Catalan
envelope. -/
theorem le_catalanEnvelope_of_quadratic_recurrence
    {u : ℕ → ℝ} {K L : ℝ}
    (hu0 : ∀ n, 0 ≤ u n) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hzero : u 0 ≤ K)
    (hsucc : ∀ n, u (n + 1) ≤ L * convolution u u n) :
    ∀ n, u n ≤ catalanEnvelope K L n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa using hzero
    | succ n =>
      calc
        u (n + 1) ≤ L * convolution u u n := hsucc n
        _ ≤ L * convolution (catalanEnvelope K L)
            (catalanEnvelope K L) n := by
          apply mul_le_mul_of_nonneg_left _ hL
          apply Finset.sum_le_sum
          intro ij hij
          have hadd : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
          exact mul_le_mul (ih ij.1 (by omega)) (ih ij.2 (by omega))
            (hu0 ij.2) (catalanEnvelope_nonneg hK hL ij.1)
        _ = catalanEnvelope K L (n + 1) :=
          (catalanEnvelope_succ K L n).symm

/-- Combining the diagonal comparison and the Catalan recurrence produces
the geometric certificate needed for convergence of the bivariate series. -/
theorem geometricBound_of_diagonal_quadratic_recurrence
    {a : Coeff} {u : ℕ → ℝ} {K L : ℝ}
    (ha : IsDiagonalMajorant a u)
    (hu0 : ∀ n, 0 ≤ u n) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hzero : u 0 ≤ K)
    (hsucc : ∀ n, u (n + 1) ≤ L * convolution u u n) :
    GeometricBound a K (8 * (K * L)) (8 * (K * L)) := by
  have hcat := le_catalanEnvelope_of_quadratic_recurrence
    hu0 hK hL hzero hsucc
  have hg := ha.geometricBound (s := 4 * (K * L)) hK
    (mul_nonneg (by norm_num) (mul_nonneg hK hL)) (fun n => by
      calc
        u n ≤ catalanEnvelope K L n := hcat n
        _ ≤ K * (4 * (K * L)) ^ n :=
          catalanEnvelope_le_geometric hK hL n)
  convert hg using 1 <;> ring

end

end CKDiagonalMajorant

end StressTensor
