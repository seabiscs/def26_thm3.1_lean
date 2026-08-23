import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# Iterated bivariate real power series

This file provides a small coefficient-series layer for the analytic part of a
Cauchy--Kowalevskaya argument.  A bivariate series is evaluated as an iterated
series: first in `y`, then in `x`.  Absolute convergence is recorded by
explicit nonnegative majorants on a closed box.  Termwise differentiation is
proved on the corresponding open box under separately stated weighted
summability hypotheses.

Nothing here proves that coefficients produced by a formal CK recursion meet
those hypotheses.  In particular, this file contains no CK convergence claim.
-/

namespace StressTensor

namespace CKPowerSeries

noncomputable section

/-- Coefficients `a m n` of the monomial `x^m y^n`. -/
abbrev Coeff := ℕ → ℕ → ℝ

/-- A single bivariate monomial. -/
def monomial (a : Coeff) (m n : ℕ) (x y : ℝ) : ℝ :=
  a m n * x ^ m * y ^ n

/-- The `n`-th term in the `y` series belonging to `x` row `m`. -/
def rowTerm (a : Coeff) (m n : ℕ) (y : ℝ) : ℝ :=
  a m n * y ^ n

/-- Evaluate one coefficient row as a real series in `y`. -/
def rowEval (a : Coeff) (m : ℕ) (y : ℝ) : ℝ :=
  ∑' n, rowTerm a m n y

/-- Evaluate a bivariate coefficient array, first in `y` and then in `x`. -/
def eval (a : Coeff) (x y : ℝ) : ℝ :=
  ∑' m, rowEval a m y * x ^ m

/-- The absolute majorant of row `m` at `y` radius `ry`. -/
def absRowSum (a : Coeff) (m : ℕ) (ry : ℝ) : ℝ :=
  ∑' n, |a m n| * ry ^ n

/--
Absolute summability on a box, expressed in the same iterated order as `eval`.
The radii are not required to be nonnegative by the definition; results using
this predicate state that condition explicitly.
-/
structure SummableOnBox (a : Coeff) (rx ry : ℝ) : Prop where
  row : ∀ m, Summable fun n => |a m n| * ry ^ n
  outer : Summable fun m => absRowSum a m ry * rx ^ m

/-- The formal termwise `x` derivative series. -/
def xDerivativeEval (a : Coeff) (x y : ℝ) : ℝ :=
  ∑' (m : ℕ), (m : ℝ) * rowEval a m y * x ^ (m - 1)

/-- The formal derivative of one row with respect to `y`. -/
def rowDerivativeEval (a : Coeff) (m : ℕ) (y : ℝ) : ℝ :=
  ∑' (n : ℕ), (n : ℝ) * a m n * y ^ (n - 1)

/-- The formal termwise `y` derivative series, in iterated order. -/
def yDerivativeEval (a : Coeff) (x y : ℝ) : ℝ :=
  ∑' m, rowDerivativeEval a m y * x ^ m

/-- The absolute majorant of the `y` derivative of row `m`. -/
def absYDerivativeRowSum (a : Coeff) (m : ℕ) (ry : ℝ) : ℝ :=
  ∑' (n : ℕ), |(n : ℝ) * a m n| * ry ^ (n - 1)

/-- Explicit weighted summability sufficient for termwise differentiation in `x`. -/
def SummableXDerivativeOnBox (a : Coeff) (rx ry : ℝ) : Prop :=
  Summable fun (m : ℕ) => (m : ℝ) * absRowSum a m ry * rx ^ (m - 1)

/-- Explicit iterated weighted summability sufficient for differentiation in `y`. -/
structure SummableYDerivativeOnBox (a : Coeff) (rx ry : ℝ) : Prop where
  row : ∀ m, Summable fun (n : ℕ) => |(n : ℝ) * a m n| * ry ^ (n - 1)
  outer : Summable fun m => absYDerivativeRowSum a m ry * rx ^ m

/-- A monomial has the expected derivative in `x`. -/
theorem monomial_hasDerivAt_x (a : Coeff) (m n : ℕ) (x y : ℝ) :
    HasDerivAt (fun z => monomial a m n z y)
      ((m : ℝ) * a m n * x ^ (m - 1) * y ^ n) x := by
  simpa only [monomial, mul_assoc, mul_left_comm, mul_comm] using
    (hasDerivAt_pow m x).const_mul (a m n * y ^ n)

/-- A monomial has the expected derivative in `y`. -/
theorem monomial_hasDerivAt_y (a : Coeff) (m n : ℕ) (x y : ℝ) :
    HasDerivAt (fun z => monomial a m n x z)
      ((n : ℝ) * a m n * x ^ m * y ^ (n - 1)) y := by
  simpa only [monomial, mul_assoc, mul_left_comm, mul_comm] using
    (hasDerivAt_pow n y).const_mul (a m n * x ^ m)

/-- A row term has the expected derivative. -/
theorem rowTerm_hasDerivAt (a : Coeff) (m n : ℕ) (y : ℝ) :
    HasDerivAt (fun z => rowTerm a m n z) ((n : ℝ) * a m n * y ^ (n - 1)) y := by
  simpa only [rowTerm, mul_assoc, mul_left_comm, mul_comm] using
    (hasDerivAt_pow n y).const_mul (a m n)

/-- Powers preserve an absolute-value bound by a nonnegative radius. -/
theorem abs_pow_le_pow {z r : ℝ} (hz : |z| ≤ r) (n : ℕ) :
    |z| ^ n ≤ r ^ n :=
  pow_le_pow_left₀ (abs_nonneg z) hz n

/-- A row term is bounded by its absolute box majorant. -/
theorem norm_rowTerm_le (a : Coeff) (m n : ℕ) {y ry : ℝ}
    (hy : |y| ≤ ry) :
    ‖rowTerm a m n y‖ ≤ |a m n| * ry ^ n := by
  rw [Real.norm_eq_abs, rowTerm, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (abs_pow_le_pow hy n) (abs_nonneg (a m n))

/-- Every absolute row majorant is nonnegative. -/
theorem absRowSum_nonneg (a : Coeff) (m : ℕ) {ry : ℝ} (hry : 0 ≤ ry) :
    0 ≤ absRowSum a m ry := by
  apply tsum_nonneg
  intro n
  exact mul_nonneg (abs_nonneg _) (pow_nonneg hry _)

/-- Absolute box summability implies convergence of every row inside the box. -/
theorem SummableOnBox.summable_rowTerm {a : Coeff} {rx ry y : ℝ}
    (h : SummableOnBox a rx ry) (hy : |y| ≤ ry) (m : ℕ) :
    Summable fun n => rowTerm a m n y := by
  exact (h.row m).of_norm_bounded fun n => norm_rowTerm_le a m n hy

/-- The evaluated row is bounded by its absolute majorant. -/
theorem SummableOnBox.norm_rowEval_le {a : Coeff} {rx ry y : ℝ}
    (h : SummableOnBox a rx ry) (hy : |y| ≤ ry) (m : ℕ) :
    ‖rowEval a m y‖ ≤ absRowSum a m ry := by
  apply (h.summable_rowTerm hy m).hasSum.norm_le_of_bounded (h.row m).hasSum
  intro n
  exact norm_rowTerm_le a m n hy

/-- Each outer summand is bounded by the iterated box majorant. -/
theorem SummableOnBox.norm_rowEval_mul_pow_le {a : Coeff} {rx ry x y : ℝ}
    (h : SummableOnBox a rx ry) (hx : |x| ≤ rx) (hy : |y| ≤ ry) (m : ℕ) :
    ‖rowEval a m y * x ^ m‖ ≤ absRowSum a m ry * rx ^ m := by
  rw [norm_mul, norm_pow, Real.norm_eq_abs]
  exact mul_le_mul (h.norm_rowEval_le hy m) (abs_pow_le_pow hx m)
    (pow_nonneg (abs_nonneg x) _)
    (absRowSum_nonneg a m ((abs_nonneg y).trans hy))

/-- The outer series defining `eval` converges throughout the closed box. -/
theorem SummableOnBox.summable_eval {a : Coeff} {rx ry x y : ℝ}
    (h : SummableOnBox a rx ry) (hx : |x| ≤ rx) (hy : |y| ≤ ry) :
    Summable fun m => rowEval a m y * x ^ m := by
  exact h.outer.of_norm_bounded fun m => h.norm_rowEval_mul_pow_le hx hy m

/-- A monomial is bounded by the corresponding absolute box weight. -/
theorem norm_monomial_le (a : Coeff) (m n : ℕ) {rx ry x y : ℝ}
    (hx : |x| ≤ rx) (hy : |y| ≤ ry) :
    ‖monomial a m n x y‖ ≤ |a m n| * rx ^ m * ry ^ n := by
  rw [Real.norm_eq_abs, monomial, abs_mul, abs_mul, abs_pow, abs_pow]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (abs_pow_le_pow hx m) (abs_nonneg (a m n)))
    (abs_pow_le_pow hy n) (pow_nonneg (abs_nonneg y) _)
    (mul_nonneg (abs_nonneg _) (pow_nonneg ((abs_nonneg x).trans hx) _))

/-- The iterated box hypothesis yields absolute summability over `ℕ × ℕ`. -/
theorem SummableOnBox.summable_absolute_product {a : Coeff} {rx ry : ℝ}
    (h : SummableOnBox a rx ry) (hrx : 0 ≤ rx) (hry : 0 ≤ ry) :
    Summable fun p : ℕ × ℕ => |a p.1 p.2| * rx ^ p.1 * ry ^ p.2 := by
  apply (summable_prod_of_nonneg (fun p =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hrx _)) (pow_nonneg hry _))).2
  constructor
  · intro m
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      (h.row m).mul_left (rx ^ m)
  · convert h.outer using 1
    funext m
    calc
      (∑' n, |a m n| * rx ^ m * ry ^ n) =
          ∑' n, (|a m n| * ry ^ n) * rx ^ m := by
            apply tsum_congr
            intro n
            ring
      _ = absRowSum a m ry * rx ^ m := by
        exact (h.row m).tsum_mul_right (rx ^ m)

/-- The full family of monomials is absolutely summable at every point of the box. -/
theorem SummableOnBox.summable_monomial_product {a : Coeff} {rx ry x y : ℝ}
    (h : SummableOnBox a rx ry) (hx : |x| ≤ rx) (hy : |y| ≤ ry) :
    Summable fun p : ℕ × ℕ => monomial a p.1 p.2 x y := by
  apply (h.summable_absolute_product ((abs_nonneg x).trans hx) ((abs_nonneg y).trans hy)).of_norm_bounded
  intro p
  exact norm_monomial_le a p.1 p.2 hx hy

/-- A term of a `y`-derivative row is bounded by its weighted majorant. -/
theorem norm_rowDerivativeTerm_le (a : Coeff) (m n : ℕ) {y ry : ℝ}
    (hy : |y| ≤ ry) :
    ‖(n : ℝ) * a m n * y ^ (n - 1)‖ ≤
      |(n : ℝ) * a m n| * ry ^ (n - 1) := by
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (abs_pow_le_pow hy (n - 1))
    (abs_nonneg ((n : ℝ) * a m n))

/-- Weighted `y`-derivative summability gives convergence of each derivative row. -/
theorem SummableYDerivativeOnBox.summable_rowDerivativeTerm
    {a : Coeff} {rx ry y : ℝ} (h : SummableYDerivativeOnBox a rx ry)
    (hy : |y| ≤ ry) (m : ℕ) :
    Summable fun (n : ℕ) => (n : ℝ) * a m n * y ^ (n - 1) := by
  exact (h.row m).of_norm_bounded fun n => norm_rowDerivativeTerm_le a m n hy

/-- The evaluated derivative row is bounded by its absolute weighted majorant. -/
theorem SummableYDerivativeOnBox.norm_rowDerivativeEval_le
    {a : Coeff} {rx ry y : ℝ} (h : SummableYDerivativeOnBox a rx ry)
    (hy : |y| ≤ ry) (m : ℕ) :
    ‖rowDerivativeEval a m y‖ ≤ absYDerivativeRowSum a m ry := by
  apply (h.summable_rowDerivativeTerm hy m).hasSum.norm_le_of_bounded (h.row m).hasSum
  intro n
  exact norm_rowDerivativeTerm_le a m n hy

/-- Every absolute `y`-derivative row majorant is nonnegative. -/
theorem absYDerivativeRowSum_nonneg (a : Coeff) (m : ℕ) {ry : ℝ} (hry : 0 ≤ ry) :
    0 ≤ absYDerivativeRowSum a m ry := by
  apply tsum_nonneg
  intro n
  exact mul_nonneg (abs_nonneg _) (pow_nonneg hry _)

/--
Termwise differentiation of a row.  The derivative is valid strictly inside
the radius on which both the row and its weighted derivative are summable.
-/
theorem hasDerivAt_rowEval {a : Coeff} {rx ry y : ℝ}
    (h : SummableOnBox a rx ry) (hdy : SummableYDerivativeOnBox a rx ry)
    (hry : 0 < ry) (hy : |y| < ry) (m : ℕ) :
    HasDerivAt (fun z => rowEval a m z) (rowDerivativeEval a m y) y := by
  have hresult := hasDerivAt_tsum_of_isPreconnected
    (hdy.row m) isOpen_Ioo isPreconnected_Ioo
    (fun n z _hz => rowTerm_hasDerivAt a m n z)
    (fun n z hz => norm_rowDerivativeTerm_le a m n (abs_lt.mpr hz).le)
    (show 0 ∈ Set.Ioo (-ry) ry by constructor <;> linarith)
    (h.summable_rowTerm (by simpa using hry.le) m)
    (show y ∈ Set.Ioo (-ry) ry from abs_lt.mp hy)
  simpa only [rowEval, rowDerivativeEval] using hresult

/-- The derivative of a convergent row is its termwise derivative series. -/
theorem deriv_rowEval {a : Coeff} {rx ry y : ℝ}
    (h : SummableOnBox a rx ry) (hdy : SummableYDerivativeOnBox a rx ry)
    (hry : 0 < ry) (hy : |y| < ry) (m : ℕ) :
    deriv (fun z => rowEval a m z) y = rowDerivativeEval a m y :=
  (hasDerivAt_rowEval h hdy hry hy m).deriv

/-- An outer row summand has the expected derivative in `x`. -/
theorem rowEval_mul_pow_hasDerivAt_x (a : Coeff) (m : ℕ) (x y : ℝ) :
    HasDerivAt (fun z => rowEval a m y * z ^ m)
      ((m : ℝ) * rowEval a m y * x ^ (m - 1)) x := by
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (hasDerivAt_pow m x).const_mul (rowEval a m y)

/-- An outer `x`-derivative term is controlled by its weighted box majorant. -/
theorem SummableOnBox.norm_xDerivativeTerm_le {a : Coeff} {rx ry x y : ℝ}
    (h : SummableOnBox a rx ry) (hx : |x| ≤ rx) (hy : |y| ≤ ry) (m : ℕ) :
    ‖(m : ℝ) * rowEval a m y * x ^ (m - 1)‖ ≤
      (m : ℝ) * absRowSum a m ry * rx ^ (m - 1) := by
  simp only [norm_mul, norm_pow, Real.norm_eq_abs]
  rw [abs_of_nonneg (show 0 ≤ (m : ℝ) by positivity)]
  rw [mul_assoc, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
  exact mul_le_mul (h.norm_rowEval_le hy m) (abs_pow_le_pow hx (m - 1))
    (pow_nonneg (abs_nonneg x) _)
    (absRowSum_nonneg a m ((abs_nonneg y).trans hy))

/-- The formal `x`-derivative series converges throughout the closed box. -/
theorem SummableXDerivativeOnBox.summable_xDerivativeTerms
    {a : Coeff} {rx ry x y : ℝ} (hdx : SummableXDerivativeOnBox a rx ry)
    (h : SummableOnBox a rx ry) (hx : |x| ≤ rx) (hy : |y| ≤ ry) :
    Summable fun (m : ℕ) => (m : ℝ) * rowEval a m y * x ^ (m - 1) := by
  exact hdx.of_norm_bounded fun m => h.norm_xDerivativeTerm_le hx hy m

/--
Termwise differentiation of the iterated bivariate series in `x`, under an
explicit weighted majorant for the differentiated outer series.
-/
theorem hasDerivAt_eval_x {a : Coeff} {rx ry x y : ℝ}
    (h : SummableOnBox a rx ry) (hdx : SummableXDerivativeOnBox a rx ry)
    (hrx : 0 < rx) (hx : |x| < rx) (hy : |y| ≤ ry) :
    HasDerivAt (fun z => eval a z y) (xDerivativeEval a x y) x := by
  have hresult := hasDerivAt_tsum_of_isPreconnected
    hdx isOpen_Ioo isPreconnected_Ioo
    (fun m z _hz => rowEval_mul_pow_hasDerivAt_x a m z y)
    (fun m z hz => h.norm_xDerivativeTerm_le (abs_lt.mpr hz).le hy m)
    (show 0 ∈ Set.Ioo (-rx) rx by constructor <;> linarith)
    (h.summable_eval (by simpa using hrx.le) hy)
    (show x ∈ Set.Ioo (-rx) rx from abs_lt.mp hx)
  simpa only [eval, xDerivativeEval] using hresult

/-- The `x` derivative is the explicitly defined termwise derivative series. -/
theorem deriv_eval_x {a : Coeff} {rx ry x y : ℝ}
    (h : SummableOnBox a rx ry) (hdx : SummableXDerivativeOnBox a rx ry)
    (hrx : 0 < rx) (hx : |x| < rx) (hy : |y| ≤ ry) :
    deriv (fun z => eval a z y) x = xDerivativeEval a x y :=
  (hasDerivAt_eval_x h hdx hrx hx hy).deriv

/-- The definition of `eval` is the expected iterated sum of monomials. -/
theorem SummableOnBox.eval_eq_iterated_monomial {a : Coeff} {rx ry x y : ℝ}
    (h : SummableOnBox a rx ry) (hy : |y| ≤ ry) :
    eval a x y = ∑' m, ∑' n, monomial a m n x y := by
  unfold eval
  apply tsum_congr
  intro m
  calc
    rowEval a m y * x ^ m = ∑' n, rowTerm a m n y * x ^ m := by
      exact ((h.summable_rowTerm hy m).tsum_mul_right (x ^ m)).symm
    _ = ∑' n, monomial a m n x y := by
      apply tsum_congr
      intro n
      simp only [rowTerm, monomial]
      ring

/-- On the box, iterated evaluation equals the unconditional sum over `ℕ × ℕ`. -/
theorem SummableOnBox.eval_eq_tsum_monomial_product {a : Coeff} {rx ry x y : ℝ}
    (h : SummableOnBox a rx ry) (hx : |x| ≤ rx) (hy : |y| ≤ ry) :
    eval a x y = ∑' p : ℕ × ℕ, monomial a p.1 p.2 x y := by
  calc
    eval a x y = ∑' m, ∑' n, monomial a m n x y := h.eval_eq_iterated_monomial hy
    _ = ∑' p : ℕ × ℕ, monomial a p.1 p.2 x y := by
      exact (h.summable_monomial_product hx hy).tsum_prod.symm

/-- Multiplying an evaluated row by a fixed `x` monomial preserves its `y` derivative. -/
theorem rowEval_mul_pow_hasDerivAt_y {a : Coeff} {rx ry y : ℝ}
    (h : SummableOnBox a rx ry) (hdy : SummableYDerivativeOnBox a rx ry)
    (hry : 0 < ry) (hy : |y| < ry) (m : ℕ) (x : ℝ) :
    HasDerivAt (fun z => rowEval a m z * x ^ m)
      (rowDerivativeEval a m y * x ^ m) y :=
  (hasDerivAt_rowEval h hdy hry hy m).mul_const (x ^ m)

/-- An outer `y`-derivative term is controlled by its iterated weighted majorant. -/
theorem SummableYDerivativeOnBox.norm_yDerivativeTerm_le
    {a : Coeff} {rx ry x y : ℝ} (hdy : SummableYDerivativeOnBox a rx ry)
    (hx : |x| ≤ rx) (hy : |y| ≤ ry) (m : ℕ) :
    ‖rowDerivativeEval a m y * x ^ m‖ ≤
      absYDerivativeRowSum a m ry * rx ^ m := by
  rw [norm_mul, norm_pow, Real.norm_eq_abs]
  exact mul_le_mul (hdy.norm_rowDerivativeEval_le hy m) (abs_pow_le_pow hx m)
    (pow_nonneg (abs_nonneg x) _)
    (absYDerivativeRowSum_nonneg a m ((abs_nonneg y).trans hy))

/-- The formal `y`-derivative series converges throughout the closed box. -/
theorem SummableYDerivativeOnBox.summable_yDerivativeTerms
    {a : Coeff} {rx ry x y : ℝ} (hdy : SummableYDerivativeOnBox a rx ry)
    (hx : |x| ≤ rx) (hy : |y| ≤ ry) :
    Summable fun m => rowDerivativeEval a m y * x ^ m := by
  exact hdy.outer.of_norm_bounded fun m => hdy.norm_yDerivativeTerm_le hx hy m

/--
Termwise differentiation of the iterated bivariate series in `y`.  Both the
inner derivative rows and their outer absolute majorant are explicit
hypotheses of `SummableYDerivativeOnBox`.
-/
theorem hasDerivAt_eval_y {a : Coeff} {rx ry x y : ℝ}
    (h : SummableOnBox a rx ry) (hdy : SummableYDerivativeOnBox a rx ry)
    (hry : 0 < ry) (hx : |x| ≤ rx) (hy : |y| < ry) :
    HasDerivAt (fun z => eval a x z) (yDerivativeEval a x y) y := by
  have hresult := hasDerivAt_tsum_of_isPreconnected
    hdy.outer isOpen_Ioo isPreconnected_Ioo
    (fun m z hz => rowEval_mul_pow_hasDerivAt_y h hdy hry (abs_lt.mpr hz) m x)
    (fun m z hz => hdy.norm_yDerivativeTerm_le hx (abs_lt.mpr hz).le m)
    (show 0 ∈ Set.Ioo (-ry) ry by constructor <;> linarith)
    (h.summable_eval hx (by simpa using hry.le))
    (show y ∈ Set.Ioo (-ry) ry from abs_lt.mp hy)
  simpa only [eval, yDerivativeEval] using hresult

/-- The `y` derivative is the explicitly defined iterated derivative series. -/
theorem deriv_eval_y {a : Coeff} {rx ry x y : ℝ}
    (h : SummableOnBox a rx ry) (hdy : SummableYDerivativeOnBox a rx ry)
    (hry : 0 < ry) (hx : |x| ≤ rx) (hy : |y| < ry) :
    deriv (fun z => eval a x z) y = yDerivativeEval a x y :=
  (hasDerivAt_eval_y h hdy hry hx hy).deriv

end

end CKPowerSeries

end StressTensor
