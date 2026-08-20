import StressTensor.CKGeometricMajorant
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Analyticity of geometrically bounded bivariate coefficient series

This file turns the product-geometric convergence certificate from
`CKGeometricMajorant` into genuine real analyticity of `CKPowerSeries.eval`.

The bridge is a homogeneous formal multilinear series on `ℝ × ℝ`. Its
degree-`k` term is the sum of all monomials `x^m y^(k-m)`. After dividing the
coefficients by positive geometric rates, its `k`-th operator norm is bounded
by `(k + 1) M`; hence its convergence radius is at least one. Composing its
analytic sum with the diagonal rate rescaling recovers the original iterated
bivariate series on every strictly smaller box.
-/

namespace StressTensor
namespace CKAnalyticEvaluation

open CKPowerSeries CKGeometricMajorant
open scoped BigOperators

noncomputable section

/-- The ordered polar monomial with `m` first-coordinate slots followed by
second-coordinate slots. Only the case `m ≤ k` is used below. -/
def polarMonomial (k m : ℕ) : (ℝ × ℝ)[×k]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ k ℝ).compContinuousLinearMap
    (fun i => if (i : ℕ) < m then ContinuousLinearMap.fst ℝ ℝ ℝ
      else ContinuousLinearMap.snd ℝ ℝ ℝ)

lemma polarMonomial_apply_prod (k m : ℕ) (x y : ℝ) :
    polarMonomial k m (fun _ => (x, y)) =
      ∏ i : Fin k, if (i : ℕ) < m then x else y := by
  simp only [polarMonomial, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs <;> rfl

private lemma prod_fin_ite_lt (x y : ℝ) : ∀ (k m : ℕ), m ≤ k →
    (∏ i : Fin k, if (i : ℕ) < m then x else y) = x ^ m * y ^ (k - m) := by
  intro k
  induction k with
  | zero =>
      intro m hm
      have : m = 0 := Nat.eq_zero_of_le_zero hm
      subst m
      simp
  | succ k ih =>
      intro m hm
      cases m with
      | zero => simp
      | succ m =>
          have hm' : m ≤ k := Nat.succ_le_succ_iff.mp hm
          rw [Fin.prod_univ_succ]
          simp only [Fin.val_zero, Nat.zero_lt_succ, ↓reduceIte,
            Fin.val_succ, Nat.succ_lt_succ_iff]
          rw [ih m hm']
          have hsub : k + 1 - (m + 1) = k - m := by omega
          rw [hsub, pow_succ]
          ring

lemma polarMonomial_apply_diag (k m : ℕ) (hm : m ≤ k) (x y : ℝ) :
    polarMonomial k m (fun _ => (x, y)) = x ^ m * y ^ (k - m) := by
  rw [polarMonomial_apply_prod]
  exact prod_fin_ite_lt x y k m hm

lemma polarMonomial_norm_le (k m : ℕ) : ‖polarMonomial k m‖ ≤ 1 := by
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  calc
    ‖ContinuousMultilinearMap.mkPiAlgebraFin ℝ k ℝ‖ *
        ∏ i : Fin k, ‖if (i : ℕ) < m then ContinuousLinearMap.fst ℝ ℝ ℝ
          else ContinuousLinearMap.snd ℝ ℝ ℝ‖
      ≤ 1 * 1 := by
        gcongr
        · exact (ContinuousMultilinearMap.norm_mkPiAlgebraFin_le
            (𝕜 := ℝ) (A := ℝ) (n := k)).trans (by norm_num)
        · apply Finset.prod_le_one
          · intro i hi
            exact norm_nonneg _
          · intro i hi
            split_ifs
            · exact ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
            · exact ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
    _ = 1 := by norm_num

/-- A bivariate coefficient array, grouped into homogeneous total degrees. -/
def bivariateFMS (b : ℕ → ℕ → ℝ) :
    FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ := fun k =>
  ∑ m ∈ Finset.range (k + 1), b m (k - m) • polarMonomial k m

lemma bivariateFMS_apply_diag (b : ℕ → ℕ → ℝ) (k : ℕ) (x y : ℝ) :
    bivariateFMS b k (fun _ => (x, y)) =
      ∑ m ∈ Finset.range (k + 1), b m (k - m) * x ^ m * y ^ (k - m) := by
  rw [bivariateFMS, sum_apply]
  apply Finset.sum_congr rfl
  intro m hm
  have hmk : m ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
  rw [smul_apply, polarMonomial_apply_diag k m hmk]
  simp [smul_eq_mul]
  ring

/-- Uniformly bounded bivariate coefficients give at most linear growth of
the homogeneous operator norms. -/
lemma bivariateFMS_norm_le (b : ℕ → ℕ → ℝ) (M : ℝ)
    (hb : ∀ m n, |b m n| ≤ M) (k : ℕ) :
    ‖bivariateFMS b k‖ ≤ (k + 1 : ℝ) * M := by
  rw [bivariateFMS]
  calc
    ‖∑ m ∈ Finset.range (k + 1), b m (k - m) • polarMonomial k m‖ ≤
        ∑ m ∈ Finset.range (k + 1), ‖b m (k - m) • polarMonomial k m‖ := by
      simpa using norm_sum_le (Finset.range (k + 1))
        (fun m => b m (k - m) • polarMonomial k m)
    _ ≤ ∑ _m ∈ Finset.range (k + 1), M := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |b m (k - m)| * ‖polarMonomial k m‖ ≤ |b m (k - m)| * 1 := by
          gcongr
          exact polarMonomial_norm_le k m
        _ ≤ M := by simpa using hb m (k - m)
    _ = (k + 1 : ℝ) * M := by simp

/-- Uniformly bounded coefficients make the associated homogeneous formal
multilinear series converge on the open unit ball. -/
lemma one_le_radius_bivariateFMS (b : ℕ → ℕ → ℝ) (M : ℝ)
    (hb : ∀ m n, |b m n| ≤ M) :
    (1 : ENNReal) ≤ (bivariateFMS b).radius := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  have hrreal : (r : ℝ) < 1 := by exact_mod_cast hr
  have hrnorm : ‖(r : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg]
    exact hrreal
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  have hgeom : Summable (fun k : ℕ => (r : ℝ) ^ k) :=
    summable_geometric_of_norm_lt_one hrnorm
  have hlinear : Summable (fun k : ℕ => (k : ℝ) * (r : ℝ) ^ k) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrnorm
  have hmajor : Summable (fun k : ℕ => ((k : ℝ) + 1) * M * (r : ℝ) ^ k) := by
    have := (hlinear.add hgeom).mul_right M
    apply this.congr
    intro k
    ring
  exact hmajor.of_norm_bounded fun k => by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ ‖bivariateFMS b k‖ * (r : ℝ) ^ k)]
    calc
      ‖bivariateFMS b k‖ * (r : ℝ) ^ k ≤
          ((k + 1 : ℝ) * M) * (r : ℝ) ^ k := by
        exact mul_le_mul_of_nonneg_right (bivariateFMS_norm_le b M hb k)
          (pow_nonneg r.coe_nonneg k)
      _ = ((k : ℝ) + 1) * M * (r : ℝ) ^ k := by ring

/-- Regroup an absolutely summable family on `ℕ × ℕ` by total degree. -/
private lemma tsum_antidiagonal_eq_tsum_prod
    (f : ℕ × ℕ → ℝ) (hf : Summable f) :
    (∑' k : ℕ, ∑ m ∈ Finset.range (k + 1), f (m, k - m)) =
      ∑' p : ℕ × ℕ, f p := by
  have hgroup := hf.hasSum.tsum_fiberwise (fun p : ℕ × ℕ => p.1 + p.2)
  have hfiber : ∀ k : ℕ,
      (∑' p : (fun p : ℕ × ℕ => p.1 + p.2) ⁻¹' ({k} : Set ℕ), f p) =
        ∑ p ∈ Finset.antidiagonal k, f p := by
    intro k
    calc
      (∑' p : {p : ℕ × ℕ // p.1 + p.2 ∈ ({k} : Set ℕ)}, f p) =
          ∑' p : ℕ × ℕ,
            ({p : ℕ × ℕ | p.1 + p.2 ∈ ({k} : Set ℕ)}).indicator f p :=
        tsum_subtype _ f
      _ = ∑ p ∈ Finset.antidiagonal k, f p := by
        rw [tsum_eq_sum (s := Finset.antidiagonal k)]
        · apply Finset.sum_congr rfl
          intro p hp
          have heq : p.1 + p.2 = k := Finset.mem_antidiagonal.mp hp
          simp [heq]
        · intro p hp
          simp only [Set.indicator]
          split_ifs with hmem
          · have heq : p.1 + p.2 = k := by simpa using hmem
            exact (hp (Finset.mem_antidiagonal.mpr heq)).elim
          · rfl
  have hrange : ∀ k : ℕ,
      (∑ p ∈ Finset.antidiagonal k, f p) =
        ∑ m ∈ Finset.range (k + 1), f (m, k - m) := by
    intro k
    simpa using Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun m n => f (m, n)) k
  have hsum : HasSum
      (fun k : ℕ => ∑ m ∈ Finset.range (k + 1), f (m, k - m))
      (∑' p : ℕ × ℕ, f p) := by
    exact HasSum.congr_fun hgroup (fun k => by
      simpa using ((hfiber k).trans (hrange k)).symm)
  exact hsum.tsum_eq

/-- Remove the geometric rates from a coefficient array. -/
def normalizedCoeff (a : Coeff) (sx sy : ℝ) : Coeff :=
  fun m n => a m n / (sx ^ m * sy ^ n)

lemma normalizedCoeff_bound {a : Coeff} {M sx sy : ℝ}
    (h : GeometricBound a M sx sy) (hsx : 0 < sx) (hsy : 0 < sy) :
    ∀ m n, |normalizedCoeff a sx sy m n| ≤ M := by
  intro m n
  have hden : 0 < sx ^ m * sy ^ n := mul_pos (pow_pos hsx _) (pow_pos hsy _)
  rw [normalizedCoeff, abs_div, abs_of_pos hden]
  exact (div_le_iff₀ hden).2 (by simpa [mul_assoc] using h.bound m n)

/-- The diagonal linear rescaling `(x, y) ↦ (sx*x, sy*y)`. -/
def rateScale (sx sy : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (sx • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (sy • ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] lemma rateScale_apply (sx sy : ℝ) (p : ℝ × ℝ) :
    rateScale sx sy p = (sx * p.1, sy * p.2) := by
  rfl

private lemma normalizedCoeff_monomial {a : Coeff} {sx sy : ℝ}
    (hsx : 0 < sx) (hsy : 0 < sy) (m n : ℕ) (x y : ℝ) :
    normalizedCoeff a sx sy m n * (sx * x) ^ m * (sy * y) ^ n =
      monomial a m n x y := by
  rw [normalizedCoeff, monomial, mul_pow, mul_pow]
  field_simp [ne_of_gt hsx, ne_of_gt hsy]

/-- On a smaller box, the homogeneous FMS sum of the normalized coefficients
and rescaled variables is exactly the original iterated bivariate sum. -/
lemma bivariateFMS_sum_rateScale_eq_eval
    {a : Coeff} {M sx sy rx ry : ℝ} (h : GeometricBound a M sx sy)
    (hsx : 0 < sx) (hsy : 0 < sy)
    (hrx : 0 ≤ rx) (hry : 0 ≤ ry)
    (hx : sx * rx < 1) (hy : sy * ry < 1)
    {x y : ℝ} (hxb : |x| ≤ rx) (hyb : |y| ≤ ry) :
    (bivariateFMS (normalizedCoeff a sx sy)).sum (rateScale sx sy (x, y)) =
      eval a x y := by
  have hbox := h.summableOnBox hrx hry hx hy
  have hsumm : Summable (fun p : ℕ × ℕ => monomial a p.1 p.2 x y) :=
    hbox.summable_monomial_product hxb hyb
  calc
    (bivariateFMS (normalizedCoeff a sx sy)).sum (rateScale sx sy (x, y)) =
        ∑' k : ℕ, ∑ m ∈ Finset.range (k + 1),
          normalizedCoeff a sx sy m (k - m) *
            (sx * x) ^ m * (sy * y) ^ (k - m) := by
      unfold FormalMultilinearSeries.sum
      apply tsum_congr
      intro k
      simpa using bivariateFMS_apply_diag
        (normalizedCoeff a sx sy) k (sx * x) (sy * y)
    _ = ∑' k : ℕ, ∑ m ∈ Finset.range (k + 1),
          monomial a m (k - m) x y := by
      apply tsum_congr
      intro k
      apply Finset.sum_congr rfl
      intro m hm
      exact normalizedCoeff_monomial hsx hsy m (k - m) x y
    _ = ∑' p : ℕ × ℕ, monomial a p.1 p.2 x y :=
      tsum_antidiagonal_eq_tsum_prod _ hsumm
    _ = eval a x y := (hbox.eval_eq_tsum_monomial_product hxb hyb).symm

private lemma rateScale_norm_lt_one
    {sx sy rx ry : ℝ} (hsx : 0 < sx) (hsy : 0 < sy)
    (hx : sx * rx < 1) (hy : sy * ry < 1)
    {p : ℝ × ℝ} (hp : p ∈ Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry) :
    ‖rateScale sx sy p‖ < 1 := by
  rw [rateScale_apply, Prod.norm_def, max_lt_iff]
  constructor
  · rw [norm_mul, Real.norm_eq_abs, abs_of_pos hsx]
    exact (mul_lt_mul_of_pos_left (abs_lt.mpr hp.1) hsx).trans hx
  · rw [norm_mul, Real.norm_eq_abs, abs_of_pos hsy]
    exact (mul_lt_mul_of_pos_left (abs_lt.mpr hp.2) hsy).trans hy

lemma rateScale_mapsTo_eball
    {sx sy rx ry : ℝ} (hsx : 0 < sx) (hsy : 0 < sy)
    (hx : sx * rx < 1) (hy : sy * ry < 1)
    {q : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ} (hq : (1 : ENNReal) ≤ q.radius) :
    Set.MapsTo (rateScale sx sy)
      (Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry)
      (Metric.eball 0 q.radius) := by
  intro p hp
  rw [Metric.mem_eball, edist_zero_right]
  calc
    ‖rateScale sx sy p‖ₑ = ENNReal.ofReal ‖rateScale sx sy p‖ :=
      (ofReal_norm _).symm
    _ < 1 := ENNReal.ofReal_lt_one.mpr
      (rateScale_norm_lt_one hsx hsy hx hy hp)
    _ ≤ q.radius := hq

end

end CKAnalyticEvaluation

namespace CKGeometricMajorant
namespace GeometricBound

open CKPowerSeries CKAnalyticEvaluation

/-- With positive rates, a product-geometric coefficient bound makes the
bivariate evaluation real analytic on every strictly smaller box. -/
theorem analyticOnNhd_eval_of_pos_rates
    {a : Coeff} {M sx sy rx ry : ℝ} (h : GeometricBound a M sx sy)
    (hsx : 0 < sx) (hsy : 0 < sy)
    (hrx : 0 < rx) (hry : 0 < ry)
    (hx : sx * rx < 1) (hy : sy * ry < 1) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ => eval a p.1 p.2)
      (Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry) := by
  let q := bivariateFMS (normalizedCoeff a sx sy)
  have hq : (1 : ENNReal) ≤ q.radius := by
    exact one_le_radius_bivariateFMS _ M
      (normalizedCoeff_bound h hsx hsy)
  have hscale : AnalyticOnNhd ℝ (rateScale sx sy)
      (Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry) := by
    intro p hp
    exact (rateScale sx sy).analyticAt p
  have hcomp : AnalyticOnNhd ℝ (q.sum ∘ rateScale sx sy)
      (Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry) :=
    FormalMultilinearSeries.analyticOnNhd.comp hscale
      (rateScale_mapsTo_eball hsx hsy hx hy hq)
  apply hcomp.congr (isOpen_Ioo.prod isOpen_Ioo)
  intro p hp
  change q.sum (rateScale sx sy p) = eval a p.1 p.2
  exact bivariateFMS_sum_rateScale_eq_eval h hsx hsy hrx.le hry.le hx hy
    (abs_lt.mpr hp.1).le (abs_lt.mpr hp.2).le

/-- Any nonnegative geometric rates can be enlarged to positive ones. -/
lemma enlargeRates
    {a : Coeff} {M sx sy : ℝ} (h : GeometricBound a M sx sy) :
    GeometricBound a M (sx + 1) (sy + 1) := by
  refine ⟨h.M_nonneg, by linarith [h.sx_nonneg], by linarith [h.sy_nonneg], ?_⟩
  intro m n
  calc
    |a m n| ≤ M * sx ^ m * sy ^ n := h.bound m n
    _ ≤ M * (sx + 1) ^ m * (sy + 1) ^ n := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ h.sx_nonneg (by linarith) m) h.M_nonneg)
        (pow_le_pow_left₀ h.sy_nonneg (by linarith) n)
        (pow_nonneg h.sy_nonneg n)
        (mul_nonneg h.M_nonneg (pow_nonneg (by linarith [h.sx_nonneg]) m))

/-- A product-geometric coefficient bound makes the bivariate evaluation
real analytic on each box that is strictly smaller for the harmlessly
enlarged positive rates `sx + 1` and `sy + 1`. This version also covers a
zero rate. -/
theorem analyticOnNhd_eval
    {a : Coeff} {M sx sy rx ry : ℝ} (h : GeometricBound a M sx sy)
    (hrx : 0 < rx) (hry : 0 < ry)
    (hx : (sx + 1) * rx < 1) (hy : (sy + 1) * ry < 1) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ => eval a p.1 p.2)
      (Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry) := by
  exact analyticOnNhd_eval_of_pos_rates
    (enlargeRates h)
    (by linarith [h.sx_nonneg]) (by linarith [h.sy_nonneg]) hrx hry hx hy

end GeometricBound
end CKGeometricMajorant
end StressTensor
