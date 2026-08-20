import StressTensor.CKPowerSeries

/-!
# Second derivatives of iterated bivariate power series

This file extends `CKPowerSeries` with direct termwise formulae for the three
second derivatives needed by the CK normal form.  Every result assumes the
corresponding weighted absolute summability explicitly.  In particular, no
claim is made here that a formally recursive coefficient array satisfies these
hypotheses.
-/

namespace StressTensor

namespace CKSecondDerivatives

open CKPowerSeries

noncomputable section

/-- The formal termwise second `x` derivative. -/
def xxDerivativeEval (a : Coeff) (x y : ℝ) : ℝ :=
  ∑' (m : ℕ),
    (m : ℝ) * ((m - 1 : ℕ) : ℝ) * rowEval a m y * x ^ (m - 2)

/-- The formal termwise mixed derivative. -/
def xyDerivativeEval (a : Coeff) (x y : ℝ) : ℝ :=
  ∑' (m : ℕ), (m : ℝ) * rowDerivativeEval a m y * x ^ (m - 1)

/-- The formal second derivative of one coefficient row in `y`. -/
def rowSecondDerivativeEval (a : Coeff) (m : ℕ) (y : ℝ) : ℝ :=
  ∑' (n : ℕ),
    (n : ℝ) * ((n - 1 : ℕ) : ℝ) * a m n * y ^ (n - 2)

/-- The formal termwise second `y` derivative, in iterated order. -/
def yyDerivativeEval (a : Coeff) (x y : ℝ) : ℝ :=
  ∑' m, rowSecondDerivativeEval a m y * x ^ m

/-- Explicit weighted summability sufficient for differentiating twice in `x`. -/
def SummableXXDerivativeOnBox (a : Coeff) (rx ry : ℝ) : Prop :=
  Summable fun (m : ℕ) =>
    (m : ℝ) * ((m - 1 : ℕ) : ℝ) * absRowSum a m ry * rx ^ (m - 2)

/-- Explicit weighted summability sufficient for the mixed derivative. -/
def SummableXYDerivativeOnBox (a : Coeff) (rx ry : ℝ) : Prop :=
  Summable fun (m : ℕ) =>
    (m : ℝ) * absYDerivativeRowSum a m ry * rx ^ (m - 1)

/-- The absolute majorant of the second `y` derivative of row `m`. -/
def absYYDerivativeRowSum (a : Coeff) (m : ℕ) (ry : ℝ) : ℝ :=
  ∑' (n : ℕ),
    |(n : ℝ) * ((n - 1 : ℕ) : ℝ) * a m n| * ry ^ (n - 2)

/-- Explicit iterated weighted summability sufficient for differentiating twice in `y`. -/
structure SummableYYDerivativeOnBox (a : Coeff) (rx ry : ℝ) : Prop where
  row : ∀ m, Summable fun (n : ℕ) =>
    |(n : ℝ) * ((n - 1 : ℕ) : ℝ) * a m n| * ry ^ (n - 2)
  outer : Summable fun m => absYYDerivativeRowSum a m ry * rx ^ m

/-- A first-`x`-derivative summand has the expected derivative. -/
theorem xDerivativeTerm_hasDerivAt
    (a : Coeff) (m : ℕ) (x y : ℝ) :
    HasDerivAt
      (fun z => (m : ℝ) * rowEval a m y * z ^ (m - 1))
      ((m : ℝ) * ((m - 1 : ℕ) : ℝ) * rowEval a m y * x ^ (m - 2)) x := by
  simpa only [Nat.sub_sub, one_add_one_eq_two, mul_assoc, mul_left_comm, mul_comm] using
    (hasDerivAt_pow (m - 1) x).const_mul ((m : ℝ) * rowEval a m y)

/-- An `xx` summand is controlled by its weighted box majorant. -/
theorem norm_xxDerivativeTerm_le
    {a : Coeff} {rx ry x y : ℝ} (h : SummableOnBox a rx ry)
    (hx : |x| ≤ rx) (hy : |y| ≤ ry) (m : ℕ) :
    ‖(m : ℝ) * ((m - 1 : ℕ) : ℝ) * rowEval a m y * x ^ (m - 2)‖ ≤
      (m : ℝ) * ((m - 1 : ℕ) : ℝ) * absRowSum a m ry * rx ^ (m - 2) := by
  simp only [norm_mul, norm_pow, Real.norm_eq_abs]
  rw [abs_of_nonneg (Nat.cast_nonneg m),
    abs_of_nonneg (Nat.cast_nonneg (m - 1))]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using h.norm_rowEval_le hy m)
      (mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg (m - 1))))
    (abs_pow_le_pow hx (m - 2))
    (pow_nonneg (abs_nonneg x) _)
    (mul_nonneg
      (mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg (m - 1)))
      (absRowSum_nonneg a m ((abs_nonneg y).trans hy)))

/-- The direct `xx` series converges throughout the closed box. -/
theorem SummableXXDerivativeOnBox.summable_xxDerivativeTerms
    {a : Coeff} {rx ry x y : ℝ} (hxx : SummableXXDerivativeOnBox a rx ry)
    (h : SummableOnBox a rx ry) (hx : |x| ≤ rx) (hy : |y| ≤ ry) :
    Summable fun (m : ℕ) =>
      (m : ℝ) * ((m - 1 : ℕ) : ℝ) * rowEval a m y * x ^ (m - 2) := by
  exact hxx.of_norm_bounded fun m => norm_xxDerivativeTerm_le h hx hy m

/-- Termwise differentiation of the first `x`-derivative series. -/
theorem hasDerivAt_xDerivativeEval_x
    {a : Coeff} {rx ry x y : ℝ}
    (h : SummableOnBox a rx ry)
    (hdx : SummableXDerivativeOnBox a rx ry)
    (hxx : SummableXXDerivativeOnBox a rx ry)
    (hrx : 0 < rx) (hx : |x| < rx) (hy : |y| ≤ ry) :
    HasDerivAt (fun z => xDerivativeEval a z y) (xxDerivativeEval a x y) x := by
  have hresult := hasDerivAt_tsum_of_isPreconnected
    hxx isOpen_Ioo isPreconnected_Ioo
    (fun m z _hz => xDerivativeTerm_hasDerivAt a m z y)
    (fun m z hz => norm_xxDerivativeTerm_le h (abs_lt.mpr hz).le hy m)
    (show 0 ∈ Set.Ioo (-rx) rx by constructor <;> linarith)
    (hdx.summable_xDerivativeTerms h (by simpa using hrx.le) hy)
    (show x ∈ Set.Ioo (-rx) rx from abs_lt.mp hx)
  simpa only [xDerivativeEval, xxDerivativeEval] using hresult

/-- The second `x` derivative is the direct termwise series. -/
theorem deriv_xDerivativeEval_x
    {a : Coeff} {rx ry x y : ℝ}
    (h : SummableOnBox a rx ry)
    (hdx : SummableXDerivativeOnBox a rx ry)
    (hxx : SummableXXDerivativeOnBox a rx ry)
    (hrx : 0 < rx) (hx : |x| < rx) (hy : |y| ≤ ry) :
    deriv (fun z => xDerivativeEval a z y) x = xxDerivativeEval a x y :=
  (hasDerivAt_xDerivativeEval_x h hdx hxx hrx hx hy).deriv

/-- A first-`x`-derivative summand has the expected `y` derivative. -/
theorem xDerivativeTerm_hasDerivAt_y
    {a : Coeff} {rx ry y : ℝ}
    (h : SummableOnBox a rx ry) (hdy : SummableYDerivativeOnBox a rx ry)
    (hry : 0 < ry) (hy : |y| < ry) (m : ℕ) (x : ℝ) :
    HasDerivAt
      (fun z => (m : ℝ) * rowEval a m z * x ^ (m - 1))
      ((m : ℝ) * rowDerivativeEval a m y * x ^ (m - 1)) y := by
  simpa only [mul_assoc] using
    ((hasDerivAt_rowEval h hdy hry hy m).const_mul (m : ℝ)).mul_const
      (x ^ (m - 1))

/-- A mixed-derivative summand is controlled by its weighted majorant. -/
theorem norm_xyDerivativeTerm_le
    {a : Coeff} {rx ry x y : ℝ} (hdy : SummableYDerivativeOnBox a rx ry)
    (hx : |x| ≤ rx) (hy : |y| ≤ ry) (m : ℕ) :
    ‖(m : ℝ) * rowDerivativeEval a m y * x ^ (m - 1)‖ ≤
      (m : ℝ) * absYDerivativeRowSum a m ry * rx ^ (m - 1) := by
  simp only [norm_mul, norm_pow, Real.norm_eq_abs]
  rw [abs_of_nonneg (Nat.cast_nonneg m)]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using hdy.norm_rowDerivativeEval_le hy m)
      (Nat.cast_nonneg m))
    (abs_pow_le_pow hx (m - 1))
    (pow_nonneg (abs_nonneg x) _)
    (mul_nonneg (Nat.cast_nonneg m)
      (absYDerivativeRowSum_nonneg a m ((abs_nonneg y).trans hy)))

/-- The direct mixed-derivative series converges throughout the closed box. -/
theorem SummableXYDerivativeOnBox.summable_xyDerivativeTerms
    {a : Coeff} {rx ry x y : ℝ} (hxy : SummableXYDerivativeOnBox a rx ry)
    (hdy : SummableYDerivativeOnBox a rx ry)
    (hx : |x| ≤ rx) (hy : |y| ≤ ry) :
    Summable fun (m : ℕ) =>
      (m : ℝ) * rowDerivativeEval a m y * x ^ (m - 1) := by
  exact hxy.of_norm_bounded fun m => norm_xyDerivativeTerm_le hdy hx hy m

/-- Differentiating the `x`-derivative series in `y` gives the mixed series. -/
theorem hasDerivAt_xDerivativeEval_y
    {a : Coeff} {rx ry x y : ℝ}
    (h : SummableOnBox a rx ry)
    (hdx : SummableXDerivativeOnBox a rx ry)
    (hdy : SummableYDerivativeOnBox a rx ry)
    (hxy : SummableXYDerivativeOnBox a rx ry)
    (hry : 0 < ry) (hx : |x| ≤ rx) (hy : |y| < ry) :
    HasDerivAt (fun z => xDerivativeEval a x z) (xyDerivativeEval a x y) y := by
  have hresult := hasDerivAt_tsum_of_isPreconnected
    hxy isOpen_Ioo isPreconnected_Ioo
    (fun m z hz => xDerivativeTerm_hasDerivAt_y h hdy hry (abs_lt.mpr hz) m x)
    (fun m z hz => norm_xyDerivativeTerm_le hdy hx (abs_lt.mpr hz).le m)
    (show 0 ∈ Set.Ioo (-ry) ry by constructor <;> linarith)
    (hdx.summable_xDerivativeTerms h hx (by simpa using hry.le))
    (show y ∈ Set.Ioo (-ry) ry from abs_lt.mp hy)
  simpa only [xDerivativeEval, xyDerivativeEval] using hresult

/-- A first-`y`-derivative outer summand has the expected `x` derivative. -/
theorem yDerivativeTerm_hasDerivAt_x
    (a : Coeff) (m : ℕ) (x y : ℝ) :
    HasDerivAt (fun z => rowDerivativeEval a m y * z ^ m)
      ((m : ℝ) * rowDerivativeEval a m y * x ^ (m - 1)) x := by
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (hasDerivAt_pow m x).const_mul (rowDerivativeEval a m y)

/-- Differentiating the `y`-derivative series in `x` gives the same mixed series. -/
theorem hasDerivAt_yDerivativeEval_x
    {a : Coeff} {rx ry x y : ℝ}
    (hdy : SummableYDerivativeOnBox a rx ry)
    (hxy : SummableXYDerivativeOnBox a rx ry)
    (hrx : 0 < rx) (hx : |x| < rx) (hy : |y| ≤ ry) :
    HasDerivAt (fun z => yDerivativeEval a z y) (xyDerivativeEval a x y) x := by
  have hresult := hasDerivAt_tsum_of_isPreconnected
    hxy isOpen_Ioo isPreconnected_Ioo
    (fun m z _hz => yDerivativeTerm_hasDerivAt_x a m z y)
    (fun m z hz => norm_xyDerivativeTerm_le hdy (abs_lt.mpr hz).le hy m)
    (show 0 ∈ Set.Ioo (-rx) rx by constructor <;> linarith)
    (hdy.summable_yDerivativeTerms (by simpa using hrx.le) hy)
    (show x ∈ Set.Ioo (-rx) rx from abs_lt.mp hx)
  simpa only [yDerivativeEval, xyDerivativeEval] using hresult

/-- A first-`y`-derivative row term has the expected derivative. -/
theorem rowDerivativeTerm_hasDerivAt
    (a : Coeff) (m n : ℕ) (y : ℝ) :
    HasDerivAt
      (fun z => (n : ℝ) * a m n * z ^ (n - 1))
      ((n : ℝ) * ((n - 1 : ℕ) : ℝ) * a m n * y ^ (n - 2)) y := by
  simpa only [Nat.sub_sub, one_add_one_eq_two, mul_assoc, mul_left_comm, mul_comm] using
    (hasDerivAt_pow (n - 1) y).const_mul ((n : ℝ) * a m n)

/-- A second-`y` row term is controlled by its weighted majorant. -/
theorem norm_rowSecondDerivativeTerm_le
    (a : Coeff) (m n : ℕ) {y ry : ℝ} (hy : |y| ≤ ry) :
    ‖(n : ℝ) * ((n - 1 : ℕ) : ℝ) * a m n * y ^ (n - 2)‖ ≤
      |(n : ℝ) * ((n - 1 : ℕ) : ℝ) * a m n| * ry ^ (n - 2) := by
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (abs_pow_le_pow hy (n - 2)) (abs_nonneg _)

/-- Weighted `yy` summability gives convergence of each second-derivative row. -/
theorem SummableYYDerivativeOnBox.summable_rowSecondDerivativeTerm
    {a : Coeff} {rx ry y : ℝ} (hyy : SummableYYDerivativeOnBox a rx ry)
    (hy : |y| ≤ ry) (m : ℕ) :
    Summable fun (n : ℕ) =>
      (n : ℝ) * ((n - 1 : ℕ) : ℝ) * a m n * y ^ (n - 2) := by
  exact (hyy.row m).of_norm_bounded fun n => norm_rowSecondDerivativeTerm_le a m n hy

/-- Every absolute second-`y` row majorant is nonnegative. -/
theorem absYYDerivativeRowSum_nonneg
    (a : Coeff) (m : ℕ) {ry : ℝ} (hry : 0 ≤ ry) :
    0 ≤ absYYDerivativeRowSum a m ry := by
  apply tsum_nonneg
  intro n
  exact mul_nonneg (abs_nonneg _) (pow_nonneg hry _)

/-- The evaluated second-derivative row is bounded by its majorant. -/
theorem SummableYYDerivativeOnBox.norm_rowSecondDerivativeEval_le
    {a : Coeff} {rx ry y : ℝ} (hyy : SummableYYDerivativeOnBox a rx ry)
    (hy : |y| ≤ ry) (m : ℕ) :
    ‖rowSecondDerivativeEval a m y‖ ≤ absYYDerivativeRowSum a m ry := by
  apply (hyy.summable_rowSecondDerivativeTerm hy m).hasSum.norm_le_of_bounded
    (hyy.row m).hasSum
  intro n
  exact norm_rowSecondDerivativeTerm_le a m n hy

/-- Termwise differentiation of a first-derivative row. -/
theorem hasDerivAt_rowDerivativeEval
    {a : Coeff} {rx ry y : ℝ}
    (hdy : SummableYDerivativeOnBox a rx ry)
    (hyy : SummableYYDerivativeOnBox a rx ry)
    (hry : 0 < ry) (hy : |y| < ry) (m : ℕ) :
    HasDerivAt (fun z => rowDerivativeEval a m z)
      (rowSecondDerivativeEval a m y) y := by
  have hresult := hasDerivAt_tsum_of_isPreconnected
    (hyy.row m) isOpen_Ioo isPreconnected_Ioo
    (fun n z _hz => rowDerivativeTerm_hasDerivAt a m n z)
    (fun n z hz => norm_rowSecondDerivativeTerm_le a m n (abs_lt.mpr hz).le)
    (show 0 ∈ Set.Ioo (-ry) ry by constructor <;> linarith)
    (hdy.summable_rowDerivativeTerm (by simpa using hry.le) m)
    (show y ∈ Set.Ioo (-ry) ry from abs_lt.mp hy)
  simpa only [rowDerivativeEval, rowSecondDerivativeEval] using hresult

/-- Multiplication by a fixed `x` monomial preserves the second row derivative. -/
theorem rowDerivativeEval_mul_pow_hasDerivAt_y
    {a : Coeff} {rx ry y : ℝ}
    (hdy : SummableYDerivativeOnBox a rx ry)
    (hyy : SummableYYDerivativeOnBox a rx ry)
    (hry : 0 < ry) (hy : |y| < ry) (m : ℕ) (x : ℝ) :
    HasDerivAt (fun z => rowDerivativeEval a m z * x ^ m)
      (rowSecondDerivativeEval a m y * x ^ m) y :=
  (hasDerivAt_rowDerivativeEval hdy hyy hry hy m).mul_const (x ^ m)

/-- An outer second-`y` term is controlled by its iterated majorant. -/
theorem SummableYYDerivativeOnBox.norm_yyDerivativeTerm_le
    {a : Coeff} {rx ry x y : ℝ} (hyy : SummableYYDerivativeOnBox a rx ry)
    (hx : |x| ≤ rx) (hy : |y| ≤ ry) (m : ℕ) :
    ‖rowSecondDerivativeEval a m y * x ^ m‖ ≤
      absYYDerivativeRowSum a m ry * rx ^ m := by
  rw [norm_mul, norm_pow, Real.norm_eq_abs]
  exact mul_le_mul (hyy.norm_rowSecondDerivativeEval_le hy m) (abs_pow_le_pow hx m)
    (pow_nonneg (abs_nonneg x) _)
    (absYYDerivativeRowSum_nonneg a m ((abs_nonneg y).trans hy))

/-- The direct `yy` series converges throughout the closed box. -/
theorem SummableYYDerivativeOnBox.summable_yyDerivativeTerms
    {a : Coeff} {rx ry x y : ℝ} (hyy : SummableYYDerivativeOnBox a rx ry)
    (hx : |x| ≤ rx) (hy : |y| ≤ ry) :
    Summable fun m => rowSecondDerivativeEval a m y * x ^ m := by
  exact hyy.outer.of_norm_bounded fun m => hyy.norm_yyDerivativeTerm_le hx hy m

/-- Differentiating the first `y`-derivative series gives the direct `yy` series. -/
theorem hasDerivAt_yDerivativeEval_y
    {a : Coeff} {rx ry x y : ℝ}
    (hdy : SummableYDerivativeOnBox a rx ry)
    (hyy : SummableYYDerivativeOnBox a rx ry)
    (hry : 0 < ry) (hx : |x| ≤ rx) (hy : |y| < ry) :
    HasDerivAt (fun z => yDerivativeEval a x z) (yyDerivativeEval a x y) y := by
  have hresult := hasDerivAt_tsum_of_isPreconnected
    hyy.outer isOpen_Ioo isPreconnected_Ioo
    (fun m z hz =>
      rowDerivativeEval_mul_pow_hasDerivAt_y hdy hyy hry (abs_lt.mpr hz) m x)
    (fun m z hz => hyy.norm_yyDerivativeTerm_le hx (abs_lt.mpr hz).le m)
    (show 0 ∈ Set.Ioo (-ry) ry by constructor <;> linarith)
    (hdy.summable_yDerivativeTerms hx (by simpa using hry.le))
    (show y ∈ Set.Ioo (-ry) ry from abs_lt.mp hy)
  simpa only [yDerivativeEval, yyDerivativeEval] using hresult

end

end CKSecondDerivatives

end StressTensor
