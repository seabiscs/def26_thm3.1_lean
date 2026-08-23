import StressTensor.CKFormalRecursion
import StressTensor.CKPowerSeries

/-!
# From formal derivative jets to ordinary bivariate coefficients

`CKFormalRecursion` uses raw mixed derivatives at the origin, while
`CKPowerSeries` evaluates ordinary monomial coefficients.  This file gives the
factorial normalization relating the two conventions and proves that all five
derivatives appearing in the normal form commute with that normalization.

The results are algebraic.  They make no summability or convergence claim.
-/

namespace StressTensor

namespace CKSeriesBridge

open CKFormalRecursion CKPowerSeries

noncomputable section

/-- The real factorial, used in Taylor-coefficient normalization. -/
def factorialReal (n : ℕ) : ℝ :=
  (n.factorial : ℝ)

theorem factorialReal_pos (n : ℕ) : 0 < factorialReal n := by
  unfold factorialReal
  exact_mod_cast Nat.factorial_pos n

theorem factorialReal_ne_zero (n : ℕ) : factorialReal n ≠ 0 :=
  (factorialReal_pos n).ne'

@[simp] theorem factorialReal_succ (n : ℕ) :
    factorialReal (n + 1) = (n + 1 : ℝ) * factorialReal n := by
  simp [factorialReal, Nat.factorial_succ]

@[simp] theorem factorialReal_add_two (n : ℕ) :
    factorialReal (n + 2) = (n + 2 : ℝ) * (n + 1 : ℝ) * factorialReal n := by
  rw [show n + 2 = (n + 1) + 1 by omega, factorialReal_succ, factorialReal_succ]
  push_cast
  ring

/--
Convert raw mixed derivatives `J m n = ∂x^m ∂y^n u(0,0)` into ordinary
Taylor coefficients `J m n / (m! n!)`.
-/
def normalize (J : FormalJet ℝ) : Coeff :=
  fun m n => J m n / (factorialReal m * factorialReal n)

/-- Shift a raw jet by one `x` derivative. -/
def shiftX (J : FormalJet ℝ) : FormalJet ℝ :=
  fun m n => J (m + 1) n

/-- Shift a raw jet by one `y` derivative. -/
def shiftY (J : FormalJet ℝ) : FormalJet ℝ :=
  fun m n => J m (n + 1)

/-- Shift a raw jet by two `x` derivatives. -/
def shiftXX (J : FormalJet ℝ) : FormalJet ℝ :=
  fun m n => J (m + 2) n

/-- Shift a raw jet by one derivative in each variable. -/
def shiftXY (J : FormalJet ℝ) : FormalJet ℝ :=
  fun m n => J (m + 1) (n + 1)

/-- Shift a raw jet by two `y` derivatives. -/
def shiftYY (J : FormalJet ℝ) : FormalJet ℝ :=
  fun m n => J m (n + 2)

/-- Ordinary monomial coefficients of the formal `x` derivative. -/
def coeffX (a : Coeff) : Coeff :=
  fun m n => (m + 1 : ℝ) * a (m + 1) n

/-- Ordinary monomial coefficients of the formal `y` derivative. -/
def coeffY (a : Coeff) : Coeff :=
  fun m n => (n + 1 : ℝ) * a m (n + 1)

/-- Ordinary monomial coefficients of the formal second `x` derivative. -/
def coeffXX (a : Coeff) : Coeff :=
  fun m n => (m + 2 : ℝ) * (m + 1 : ℝ) * a (m + 2) n

/-- Ordinary monomial coefficients of the formal mixed derivative. -/
def coeffXY (a : Coeff) : Coeff :=
  fun m n => (m + 1 : ℝ) * (n + 1 : ℝ) * a (m + 1) (n + 1)

/-- Ordinary monomial coefficients of the formal second `y` derivative. -/
def coeffYY (a : Coeff) : Coeff :=
  fun m n => (n + 2 : ℝ) * (n + 1 : ℝ) * a m (n + 2)

/-- Factorial normalization intertwines the formal `x` derivative and the `x` shift. -/
theorem coeffX_normalize (J : FormalJet ℝ) :
    coeffX (normalize J) = normalize (shiftX J) := by
  funext m n
  simp only [coeffX, normalize, shiftX, factorialReal_succ]
  field_simp [factorialReal_ne_zero]

/-- Factorial normalization intertwines the formal `y` derivative and the `y` shift. -/
theorem coeffY_normalize (J : FormalJet ℝ) :
    coeffY (normalize J) = normalize (shiftY J) := by
  funext m n
  simp only [coeffY, normalize, shiftY, factorialReal_succ]
  field_simp [factorialReal_ne_zero]

/-- Factorial normalization intertwines the second `x` derivative and the double shift. -/
theorem coeffXX_normalize (J : FormalJet ℝ) :
    coeffXX (normalize J) = normalize (shiftXX J) := by
  funext m n
  simp only [coeffXX, normalize, shiftXX, factorialReal_add_two]
  field_simp [factorialReal_ne_zero]

/-- Factorial normalization intertwines the mixed derivative and the mixed shift. -/
theorem coeffXY_normalize (J : FormalJet ℝ) :
    coeffXY (normalize J) = normalize (shiftXY J) := by
  funext m n
  simp only [coeffXY, normalize, shiftXY, factorialReal_succ]
  field_simp [factorialReal_ne_zero]

/-- Factorial normalization intertwines the second `y` derivative and the double shift. -/
theorem coeffYY_normalize (J : FormalJet ℝ) :
    coeffYY (normalize J) = normalize (shiftYY J) := by
  funext m n
  simp only [coeffYY, normalize, shiftYY, factorialReal_add_two]
  field_simp [factorialReal_ne_zero]

/-- Normalize the raw mixed-derivative rows returned by a triangular RHS. -/
def normalizedRHS (F : TriangularRHS ℝ) (J : FormalJet ℝ) : Coeff :=
  fun m n => F.coeff J m n / (factorialReal m * factorialReal n)

/--
The raw recurrence `J (m+2) n = F.coeff J m n` is exactly the conventional
power-series recurrence
`(m+2)(m+1) a (m+2) n = normalizedRHS F J m n` for `a = normalize J`.
-/
theorem coeffXX_normalize_eq_normalizedRHS
    (F : TriangularRHS ℝ) {J : FormalJet ℝ}
    (hJ : SatisfiesRecurrence F J) :
    coeffXX (normalize J) = normalizedRHS F J := by
  rw [coeffXX_normalize]
  funext m n
  simp only [normalize, shiftXX, normalizedRHS]
  rw [congrFun (hJ m) n]

/-- The normalized zeroth row is the ordinary Taylor series of the first Cauchy row. -/
theorem normalize_row_zero (J : FormalJet ℝ) (n : ℕ) :
    normalize J 0 n = J 0 n / factorialReal n := by
  simp [normalize, factorialReal]

/-- The normalized first row is the ordinary Taylor series of the second Cauchy row. -/
theorem normalize_row_one (J : FormalJet ℝ) (n : ℕ) :
    normalize J 1 n = J 1 n / factorialReal n := by
  simp [normalize, factorialReal]

/-- Raw derivative row for the zero Cauchy datum. -/
def zeroCauchyRow : Row ℝ :=
  fun _ => 0

/-- Raw derivative row for the constant Cauchy datum `u_x(0,y) = -1`. -/
def negOneCauchyRow : Row ℝ :=
  fun n => if n = 0 then -1 else 0

/-- Factorial normalization preserves the zero Cauchy row. -/
@[simp] theorem normalize_zeroCauchyRow (n : ℕ) :
    zeroCauchyRow n / factorialReal n = zeroCauchyRow n := by
  simp [zeroCauchyRow]

/-- Factorial normalization preserves the derivative row of the constant datum `-1`. -/
@[simp] theorem normalize_negOneCauchyRow (n : ℕ) :
    negOneCauchyRow n / factorialReal n = negOneCauchyRow n := by
  by_cases hn : n = 0
  · subst n
    norm_num [negOneCauchyRow, factorialReal]
  · simp [negOneCauchyRow, hn]

/-- The canonical formal solution has the prescribed normalized Cauchy coefficient rows. -/
theorem normalize_formalSolution_cauchyRows (F : TriangularRHS ℝ) :
    normalize (formalSolution F zeroCauchyRow negOneCauchyRow) 0 = zeroCauchyRow ∧
      normalize (formalSolution F zeroCauchyRow negOneCauchyRow) 1 = negOneCauchyRow := by
  constructor <;> funext n
  · rw [normalize_row_zero, formalSolution_zero]
    exact normalize_zeroCauchyRow n
  · rw [normalize_row_one, formalSolution_one]
    exact normalize_negOneCauchyRow n

end

end CKSeriesBridge

end StressTensor
