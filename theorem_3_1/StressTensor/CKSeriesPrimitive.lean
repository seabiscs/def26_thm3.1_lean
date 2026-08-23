import StressTensor.CKAnalyticEvaluation
import StressTensor.CKSeriesBridge

/-!
# Analytic zero-initial-value primitives of bivariate coefficient series

For an ordinary bivariate coefficient array `a`, integration in the
evolution variable is the exact coefficient operation

`b 0 n = 0`, `b (m+1) n = a m n / (m+1)`.

This file proves that a product-geometric bound is preserved (after a harmless
increase of the `x` rate), that formal differentiation returns `a`, and that
the analytic sums satisfy the corresponding actual derivative identity.
-/

namespace StressTensor
namespace CKSeriesPrimitive

open CKPowerSeries CKSeriesBridge CKGeometricMajorant

noncomputable section

/-- Coefficients of the zero-initial-value primitive in `x`. -/
def xPrimitiveCoeff (a : Coeff) : Coeff
  | 0, _ => 0
  | m + 1, n => a m n / (m + 1 : ℝ)

@[simp] theorem xPrimitiveCoeff_zero (a : Coeff) (n : ℕ) :
    xPrimitiveCoeff a 0 n = 0 := rfl

@[simp] theorem xPrimitiveCoeff_succ (a : Coeff) (m n : ℕ) :
    xPrimitiveCoeff a (m + 1) n = a m n / (m + 1 : ℝ) := rfl

/-- The coefficient derivative of the primitive is exactly the original
array. -/
@[simp] theorem coeffX_xPrimitiveCoeff (a : Coeff) :
    coeffX (xPrimitiveCoeff a) = a := by
  funext m n
  simp only [coeffX, xPrimitiveCoeff_succ]
  field_simp

/-- Pull the constant `x`-derivative factor through one convergent `y` row. -/
theorem rowEval_coeffX
    {a : Coeff} (m : ℕ) (y : ℝ) :
    rowEval (coeffX a) m y = (m + 1 : ℝ) * rowEval a (m + 1) y := by
  unfold rowEval rowTerm coeffX
  calc
    (∑' n, (m + 1 : ℝ) * a (m + 1) n * y ^ n) =
        ∑' n, (m + 1 : ℝ) * (a (m + 1) n * y ^ n) := by
          apply tsum_congr
          intro n
          ring
    _ = (m + 1 : ℝ) * ∑' n, a (m + 1) n * y ^ n :=
      tsum_mul_left

/-- Under the weighted summability already used for termwise calculus, the
explicit derivative evaluation is the ordinary evaluation of `coeffX a`. -/
theorem xDerivativeEval_eq_eval_coeffX
    {a : Coeff} {rx ry x y : ℝ}
    (h : SummableOnBox a rx ry)
    (hdx : SummableXDerivativeOnBox a rx ry)
    (hx : |x| ≤ rx) (hy : |y| ≤ ry) :
    xDerivativeEval a x y = eval (coeffX a) x y := by
  let f : ℕ → ℝ := fun m =>
    (m : ℝ) * rowEval a m y * x ^ (m - 1)
  have hf : Summable f := by
    exact hdx.summable_xDerivativeTerms h hx hy
  have hshift := hf.sum_add_tsum_nat_add 1
  have htail : (∑' m, f (m + 1)) = ∑' m, f m := by
    simpa [f] using hshift
  calc
    xDerivativeEval a x y = ∑' m, f m := rfl
    _ = ∑' m, f (m + 1) := htail.symm
    _ = ∑' m, rowEval (coeffX a) m y * x ^ m := by
      apply tsum_congr
      intro m
      rw [rowEval_coeffX]
      dsimp only [f]
      rw [show m + 1 - 1 = m by omega]
      push_cast
      ring
    _ = eval (coeffX a) x y := rfl

/-- Integration in `x` preserves a product-geometric bound after replacing
the `x` rate by `max 1 sx`. -/
theorem geometricBound_xPrimitiveCoeff
    {a : Coeff} {M sx sy : ℝ} (h : GeometricBound a M sx sy) :
    GeometricBound (xPrimitiveCoeff a) M (max 1 sx) sy := by
  refine ⟨h.M_nonneg, (le_max_left 1 sx).trans' (by norm_num),
    h.sy_nonneg, ?_⟩
  intro m n
  cases m with
  | zero =>
      simpa [xPrimitiveCoeff] using
        mul_nonneg h.M_nonneg (pow_nonneg h.sy_nonneg n)
  | succ m =>
      have hden : (1 : ℝ) ≤ (m + 1 : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      have hdiv : |a m n / (m + 1 : ℝ)| ≤ |a m n| := by
        rw [abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hden)]
        exact div_le_self (abs_nonneg _) hden
      have hsxT : sx ^ m ≤ (max 1 sx) ^ m :=
        pow_le_pow_left₀ h.sx_nonneg (le_max_right 1 sx) m
      have hT : (max 1 sx) ^ m ≤ (max 1 sx) ^ (m + 1) := by
        have hT0 : 0 ≤ max 1 sx :=
          le_trans (by norm_num) (le_max_left 1 sx)
        rw [pow_succ]
        exact le_mul_of_one_le_right (pow_nonneg hT0 m)
          (le_max_left 1 sx)
      calc
        |xPrimitiveCoeff a (m + 1) n| ≤ |a m n| := hdiv
        _ ≤ M * sx ^ m * sy ^ n := h.bound m n
        _ ≤ M * (max 1 sx) ^ m * sy ^ n := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsxT h.M_nonneg)
            (pow_nonneg h.sy_nonneg n)
        _ ≤ M * (max 1 sx) ^ (m + 1) * sy ^ n := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hT h.M_nonneg)
            (pow_nonneg h.sy_nonneg n)

/-- The sum of the primitive coefficients is analytic on every strictly
smaller box. -/
theorem analyticOnNhd_eval_xPrimitiveCoeff
    {a : Coeff} {M sx sy rx ry : ℝ} (h : GeometricBound a M sx sy)
    (hrx : 0 < rx) (hry : 0 < ry)
    (hxrate : (max 1 sx + 1) * rx < 1)
    (hyrate : (sy + 1) * ry < 1) :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ => eval (xPrimitiveCoeff a) p.1 p.2)
      (Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry) := by
  exact (geometricBound_xPrimitiveCoeff h).analyticOnNhd_eval
    hrx hry hxrate hyrate

/-- The primitive is analytic on the *same* enlarged-rate box as the
original series.  The apparent extra loss in
`analyticOnNhd_eval_xPrimitiveCoeff` is avoidable: the primitive coefficients
are bounded at the positive rates `(sx+1, sy+1)`, and the positive-rate
realization theorem uses those rates directly. -/
theorem analyticOnNhd_eval_xPrimitiveCoeff_same_box
    {a : Coeff} {M sx sy rx ry : ℝ} (h : GeometricBound a M sx sy)
    (hrx : 0 < rx) (hry : 0 < ry)
    (hxrate : (sx + 1) * rx < 1)
    (hyrate : (sy + 1) * ry < 1) :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ => eval (xPrimitiveCoeff a) p.1 p.2)
      (Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry) := by
  let hb := geometricBound_xPrimitiveCoeff h
  have hxmono : max 1 sx ≤ sx + 1 := by
    apply max_le
    · linarith [h.sx_nonneg]
    · linarith
  have hymono : sy ≤ sy + 1 := by linarith
  have hb' : GeometricBound (xPrimitiveCoeff a) M (sx + 1) (sy + 1) := by
    refine ⟨h.M_nonneg, by linarith [h.sx_nonneg],
      by linarith [h.sy_nonneg], ?_⟩
    intro m n
    calc
      |xPrimitiveCoeff a m n| ≤ M * (max 1 sx) ^ m * sy ^ n := hb.bound m n
      _ ≤ M * (sx + 1) ^ m * (sy + 1) ^ n := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hb.sx_nonneg hxmono m) h.M_nonneg)
          (pow_le_pow_left₀ h.sy_nonneg hymono n)
          (pow_nonneg h.sy_nonneg n)
          (mul_nonneg h.M_nonneg
            (pow_nonneg (by linarith [h.sx_nonneg]) m))
  exact hb'.analyticOnNhd_eval_of_pos_rates
    (by linarith [h.sx_nonneg]) (by linarith [h.sy_nonneg])
    hrx hry hxrate hyrate

/-- Actual differentiation of the analytic primitive returns the original
evaluated series. -/
theorem deriv_eval_xPrimitiveCoeff
    {a : Coeff} {M sx sy rx ry x y : ℝ}
    (h : GeometricBound a M sx sy)
    (hrx : 0 < rx) (hry : 0 < ry)
    (hxrate : (max 1 sx) * rx < 1) (hyrate : sy * ry < 1)
    (hx : |x| < rx) (hy : |y| ≤ ry) :
    deriv (fun z => eval (xPrimitiveCoeff a) z y) x = eval a x y := by
  let hb := geometricBound_xPrimitiveCoeff h
  have hbox := hb.summableOnBox hrx.le hry.le hxrate hyrate
  have hdx := hb.summableXDerivativeOnBox hrx hry.le hxrate hyrate
  calc
    deriv (fun z => eval (xPrimitiveCoeff a) z y) x =
        xDerivativeEval (xPrimitiveCoeff a) x y :=
      CKPowerSeries.deriv_eval_x hbox hdx hrx hx hy
    _ = eval (coeffX (xPrimitiveCoeff a)) x y :=
      xDerivativeEval_eq_eval_coeffX hbox hdx hx.le hy
    _ = eval a x y := by rw [coeffX_xPrimitiveCoeff]

/-- The analytic primitive has zero Cauchy value on the entire `x=0` axis. -/
@[simp] theorem eval_xPrimitiveCoeff_zero (a : Coeff) (y : ℝ) :
    eval (xPrimitiveCoeff a) 0 y = 0 := by
  unfold eval
  calc
    (∑' m, rowEval (xPrimitiveCoeff a) m y * 0 ^ m) =
        ∑' _m : ℕ, 0 := by
      apply tsum_congr
      intro m
      cases m with
      | zero => simp [rowEval, rowTerm]
      | succ m => simp
    _ = 0 := tsum_zero

end

end CKSeriesPrimitive
end StressTensor
