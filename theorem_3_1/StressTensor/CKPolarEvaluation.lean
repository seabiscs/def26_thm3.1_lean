import StressTensor.CKVectorAnalyticEvaluation
import StressTensor.CKFirstOrderAnalyticData
import StressTensor.CKSeriesBridge

/-!
# Polar evaluation of bivariate formal multilinear series

This file supplies the coefficient-to-function bridge used by the reduced
Cauchy--Kowalevskaya construction.  It polarizes an arbitrary homogeneous
multilinear series on `ℝ × ℝ`, regroups its diagonal sum by bivariate
coefficients, and records convergence and positive-radius statements under
product-geometric bounds.

The development is independent of the equation-specific formal recurrence.
In particular, it can be used for any two-component coefficient array once a
geometric bound has been established.
-/

namespace StressTensor
namespace CKPolarEvaluation

open CKPowerSeries CKSeriesBridge CKGeometricMajorant CKAnalyticEvaluation
open scoped BigOperators

noncomputable section

/-! ## Polar coefficients of a general homogeneous series -/

/-- Put the first coordinate vector in the slots selected by `s` and the
second coordinate vector in the remaining slots. -/
def polarSlotInput (k : ℕ) (s : Finset (Fin k)) : Fin k → ℝ × ℝ :=
  fun i => if i ∈ s then (1, 0) else (0, 1)

/-- The coefficient of `x^m y^n` obtained by polarizing the homogeneous term
of total degree `m+n`. -/
def polarCoefficient
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p : FormalMultilinearSeries ℝ (ℝ × ℝ) G) (m n : ℕ) : G :=
  ∑ s ∈ (Finset.univ : Finset (Fin (m + n))).powersetCard m,
    p (m + n) (polarSlotInput (m + n) s)

lemma map_piecewise_smul_polarSlotInput
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (q : (ℝ × ℝ)[×k]→L[ℝ] G) (s : Finset (Fin k)) (x y : ℝ) :
    q (s.piecewise (fun _ => x • ((1, 0) : ℝ × ℝ))
        (fun _ => y • ((0, 1) : ℝ × ℝ))) =
      (x ^ s.card * y ^ (k - s.card)) • q (polarSlotInput k s) := by
  have hinput :
      s.piecewise (fun _ => x • ((1, 0) : ℝ × ℝ))
          (fun _ => y • ((0, 1) : ℝ × ℝ)) =
        fun i => (if i ∈ s then x else y) • polarSlotInput k s i := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, polarSlotInput, hi]
  rw [hinput, q.map_smul_univ]
  congr 1
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
      simp only [Finset.prod_const, Finset.card_compl, Fintype.card_fin]

/-- Diagonal evaluation of a homogeneous multilinear term expands into its
polar bivariate coefficients. -/
theorem apply_diag_eq_sum_polarCoefficient
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p : FormalMultilinearSeries ℝ (ℝ × ℝ) G)
    (k : ℕ) (x y : ℝ) :
    p k (fun _ => (x, y)) =
      ∑ m ∈ Finset.range (k + 1),
        (x ^ m * y ^ (k - m)) • polarCoefficient p m (k - m) := by
  have hdiag : (fun _ : Fin k => (x, y)) =
      (fun _ => x • ((1, 0) : ℝ × ℝ)) +
        (fun _ => y • ((0, 1) : ℝ × ℝ)) := by
    funext i
    ext <;> simp
  rw [hdiag, (p k).map_add_univ]
  calc
    (∑ s : Finset (Fin k),
        p k (s.piecewise (fun _ => x • ((1, 0) : ℝ × ℝ))
          (fun _ => y • ((0, 1) : ℝ × ℝ)))) =
      ∑ s : Finset (Fin k),
        (x ^ s.card * y ^ (k - s.card)) •
          p k (polarSlotInput k s) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact map_piecewise_smul_polarSlotInput (p k) s x y
    _ = ∑ m ∈ Finset.range (k + 1),
        ∑ s ∈ (Finset.univ : Finset (Fin k)).powersetCard m,
          (x ^ s.card * y ^ (k - s.card)) •
            p k (polarSlotInput k s) := by
      symm
      have hmaps : ∀ s ∈ (Finset.univ : Finset (Finset (Fin k))),
          s.card ∈ Finset.range (k + 1) := by
        intro s hs
        simp only [Finset.mem_range]
        exact Nat.lt_succ_of_le (by simpa using Finset.card_le_univ s)
      simp_rw [Finset.powersetCard_eq_filter, Finset.powerset_univ]
      rw [Finset.sum_fiberwise_of_maps_to hmaps]
    _ = ∑ m ∈ Finset.range (k + 1),
        (x ^ m * y ^ (k - m)) • polarCoefficient p m (k - m) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmk : m ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
      rw [polarCoefficient, Nat.add_sub_of_le hmk]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [(Finset.mem_powersetCard.mp hs).2]

/-! ## Rate scaling and positive convergence radius -/

lemma polarMonomial_rateScale
    (k m : ℕ) (hm : m ≤ k) (sx sy : ℝ) (z : Fin k → ℝ × ℝ) :
    polarMonomial k m (fun i => rateScale sx sy (z i)) =
      sx ^ m * sy ^ (k - m) * polarMonomial k m z := by
  simp only [polarMonomial,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply,
    List.prod_ofFn, rateScale_apply]
  calc
    (∏ i : Fin k,
        (if (i : ℕ) < m then ContinuousLinearMap.fst ℝ ℝ ℝ
          else ContinuousLinearMap.snd ℝ ℝ ℝ) (sx * (z i).1, sy * (z i).2)) =
        ∏ i : Fin k,
          (if (i : ℕ) < m then sx else sy) *
            (if (i : ℕ) < m then (z i).1 else (z i).2) := by
      apply Finset.prod_congr rfl
      intro i hi
      split_ifs <;> rfl
    _ = (∏ i : Fin k, if (i : ℕ) < m then sx else sy) *
        ∏ i : Fin k, if (i : ℕ) < m then (z i).1 else (z i).2 := by
      rw [Finset.prod_mul_distrib]
    _ = (sx ^ m * sy ^ (k - m)) *
        ∏ i : Fin k, if (i : ℕ) < m then (z i).1 else (z i).2 := by
      have hcardx :
          (Finset.filter (fun i : Fin k => (i : ℕ) < m) Finset.univ).card = m := by
        simpa only [Nat.min_eq_right hm] using
          (@Fin.card_filter_val_lt k m)
      have hcardy :
          (Finset.filter (fun i : Fin k => ¬ (i : ℕ) < m) Finset.univ).card =
            k - m := by
        have heq : Finset.filter (fun i : Fin k => ¬ (i : ℕ) < m) Finset.univ =
            (Finset.filter (fun i : Fin k => (i : ℕ) < m) Finset.univ)ᶜ := by
          ext i
          simp
        rw [heq, Finset.card_compl, hcardx, Fintype.card_fin]
      congr 1
      calc
        (∏ i : Fin k, if (i : ℕ) < m then sx else sy) =
        (∏ i ∈ Finset.filter (fun i : Fin k => (i : ℕ) < m) Finset.univ, sx) *
          ∏ i ∈ Finset.filter (fun i : Fin k => ¬ (i : ℕ) < m) Finset.univ, sy := by
          rw [Finset.prod_ite]
        _ = sx ^ m * sy ^ (k - m) := by
          simp only [Finset.prod_const]
          rw [hcardx, hcardy]
    _ = sx ^ m * sy ^ (k - m) *
        ∏ i : Fin k,
          (if (i : ℕ) < m then ContinuousLinearMap.fst ℝ ℝ ℝ
            else ContinuousLinearMap.snd ℝ ℝ ℝ) (z i) := by
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      split_ifs <;> rfl

/-- Scaling out positive geometric rates realizes the original FMS as a
continuous-linear reparametrization of its normalized FMS. -/
theorem bivariateFMS_eq_comp_rateScale
    (a : Coeff) {sx sy : ℝ} (hsx : 0 < sx) (hsy : 0 < sy) :
    bivariateFMS a =
      (bivariateFMS (normalizedCoeff a sx sy)).compContinuousLinearMap
        (rateScale sx sy) := by
  funext k
  ext z
  simp only [bivariateFMS,
    FormalMultilinearSeries.compContinuousLinearMap_apply,
    sum_apply, smul_apply]
  apply Finset.sum_congr rfl
  intro m hm
  have hmk : m ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
  change a m (k - m) * polarMonomial k m z =
    normalizedCoeff a sx sy m (k - m) *
      polarMonomial k m (fun i => rateScale sx sy (z i))
  rw [polarMonomial_rateScale k m hmk]
  simp only [normalizedCoeff]
  have hxpow : sx ^ m ≠ 0 := pow_ne_zero _ (ne_of_gt hsx)
  have hypow : sy ^ (k - m) ≠ 0 := pow_ne_zero _ (ne_of_gt hsy)
  field_simp

/-- A product-geometrically bounded coefficient array has a strictly
positive FMS convergence radius, including when one of the original rates is
zero. -/
theorem radius_bivariateFMS_pos
    {a : Coeff} {M sx sy : ℝ} (h : GeometricBound a M sx sy) :
    0 < (bivariateFMS a).radius := by
  let h' := h.enlargeRates
  have hsx' : 0 < sx + 1 := by linarith [h.sx_nonneg]
  have hsy' : 0 < sy + 1 := by linarith [h.sy_nonneg]
  let q := bivariateFMS (normalizedCoeff a (sx + 1) (sy + 1))
  have hq : (1 : ENNReal) ≤ q.radius := by
    exact one_le_radius_bivariateFMS _ M
      (normalizedCoeff_bound h' hsx' hsy')
  have hq0 : q.radius ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le hq)
  rw [bivariateFMS_eq_comp_rateScale a hsx' hsy']
  exact (ENNReal.div_pos hq0 enorm_ne_top).trans_le
    (q.div_le_radius_compContinuousLinearMap (rateScale (sx + 1) (sy + 1)))

/-! ## Regrouping and evaluation of scalar and vector series -/

/-- Regroup an absolutely summable family on `ℕ × ℕ` by its
antidiagonals, retaining a `HasSum` certificate rather than only a `tsum`
identity. -/
theorem hasSum_antidiagonal_eq_tsum_prod
    (f : ℕ × ℕ → ℝ) (hf : Summable f) :
    HasSum (fun k : ℕ => ∑ m ∈ Finset.range (k + 1), f (m, k - m))
      (∑' p : ℕ × ℕ, f p) := by
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
  exact HasSum.congr_fun hgroup (fun k => by
    simpa using ((hfiber k).trans (hrange k)).symm)

/-- A geometrically bounded bivariate coefficient array is summed by its
homogeneous FMS on every closed box strictly inside the product radius. -/
theorem hasSum_bivariateFMS
    {a : Coeff} {M sx sy rx ry x y : ℝ}
    (h : GeometricBound a M sx sy)
    (hrx : 0 ≤ rx) (hry : 0 ≤ ry)
    (hxrate : sx * rx < 1) (hyrate : sy * ry < 1)
    (hx : |x| ≤ rx) (hy : |y| ≤ ry) :
    HasSum (fun k => bivariateFMS a k (fun _ => (x, y))) (eval a x y) := by
  have hbox := h.summableOnBox hrx hry hxrate hyrate
  have hsumm : Summable (fun p : ℕ × ℕ => monomial a p.1 p.2 x y) :=
    hbox.summable_monomial_product hx hy
  have hgroup := hasSum_antidiagonal_eq_tsum_prod
    (fun p : ℕ × ℕ => monomial a p.1 p.2 x y) hsumm
  rw [hbox.eval_eq_tsum_monomial_product hx hy]
  apply hgroup.congr_fun
  intro k
  rw [bivariateFMS_apply_diag]
  apply Finset.sum_congr rfl
  intro m hm
  rfl

/-- Componentwise bivariate geometric bounds turn the diagonal sum of a
two-component polar FMS into the vector of evaluated coefficient series. -/
theorem hasSum_polarCoefficient
    (p : FormalMultilinearSeries ℝ (ℝ × ℝ) FirstOrderState)
    {M sx sy rx ry x y : ℝ}
    (h : CKVectorAnalyticEvaluation.VectorGeometricBound
      (fun i m n => polarCoefficient p m n i) M sx sy)
    (hrx : 0 ≤ rx) (hry : 0 ≤ ry)
    (hxrate : sx * rx < 1) (hyrate : sy * ry < 1)
    (hx : |x| ≤ rx) (hy : |y| ≤ ry) :
    HasSum (fun k => p k (fun _ => (x, y)))
      (fun i => eval (fun m n => polarCoefficient p m n i) x y) := by
  rw [Pi.hasSum]
  intro i
  have hs := hasSum_bivariateFMS (h.component i) hrx hry
    hxrate hyrate hx hy
  apply hs.congr_fun
  intro k
  rw [bivariateFMS_apply_diag]
  have hk := congrArg (fun v : FirstOrderState => v i)
    (apply_diag_eq_sum_polarCoefficient p k x y)
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using hk

/-! ## Differentiated and state-valued coefficient arrays -/

/-- Product-geometric control is preserved by formal `x` differentiation,
with explicit enlarged constants. -/
theorem geometricBound_coeffX
    {a : Coeff} {M sx sy : ℝ} (h : GeometricBound a M sx sy) :
    GeometricBound (coeffX a) (M * (sx + 1))
      (2 * (sx + 1)) sy := by
  have hT : 0 ≤ sx + 1 := by linarith [h.sx_nonneg]
  refine ⟨mul_nonneg h.M_nonneg hT, mul_nonneg (by norm_num) hT,
    h.sy_nonneg, ?_⟩
  intro m n
  have hnat : (m + 1 : ℝ) ≤ (2 : ℝ) ^ m := by
    exact_mod_cast (Nat.succ_le_iff.mpr m.lt_two_pow_self)
  have hsxpow : sx ^ (m + 1) ≤ (sx + 1) ^ (m + 1) :=
    pow_le_pow_left₀ h.sx_nonneg (by linarith) (m + 1)
  have hm1 : (0 : ℝ) ≤ m + 1 := by positivity
  have hsypow : 0 ≤ sy ^ n := pow_nonneg h.sy_nonneg n
  rw [coeffX, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ m + 1)]
  calc
    (m + 1 : ℝ) * |a (m + 1) n| ≤
        (m + 1 : ℝ) * (M * sx ^ (m + 1) * sy ^ n) := by
      exact mul_le_mul_of_nonneg_left (h.bound (m + 1) n) hm1
    _ ≤ (m + 1 : ℝ) * (M * (sx + 1) ^ (m + 1) * sy ^ n) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsxpow h.M_nonneg) hsypow) hm1
    _ ≤ (2 : ℝ) ^ m * (M * (sx + 1) ^ (m + 1) * sy ^ n) := by
      exact mul_le_mul_of_nonneg_right hnat
        (mul_nonneg (mul_nonneg h.M_nonneg (pow_nonneg hT _)) hsypow)
    _ = (M * (sx + 1)) * (2 * (sx + 1)) ^ m * sy ^ n := by
      rw [pow_succ, mul_pow]
      ring

/-- Bivariate coefficients valued in the reduced two-component state. -/
abbrev FirstOrderStateCoeff := ℕ → ℕ → FirstOrderState

/-- The componentwise homogeneous FMS associated with a reduced-state
coefficient array. -/
def stateFMS (a : FirstOrderStateCoeff) :
    FormalMultilinearSeries ℝ (ℝ × ℝ) FirstOrderState :=
  FormalMultilinearSeries.pi fun i =>
    bivariateFMS (fun m n => a m n i)

/-- A common geometric bound for both components gives the state FMS a
strictly positive convergence radius. -/
theorem radius_stateFMS_pos
    {a : FirstOrderStateCoeff} {M sx sy : ℝ}
    (h : CKVectorAnalyticEvaluation.VectorGeometricBound
      (fun i m n => a m n i) M sx sy) :
    0 < (stateFMS a).radius := by
  have h0 := radius_bivariateFMS_pos (h.component (0 : Fin 2))
  have h1 := radius_bivariateFMS_pos (h.component (1 : Fin 2))
  have hle : ∀ i : Fin 2,
      min (bivariateFMS (fun m n => a m n (0 : Fin 2))).radius
          (bivariateFMS (fun m n => a m n (1 : Fin 2))).radius ≤
        (bivariateFMS (fun m n => a m n i)).radius := by
    intro i
    fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  exact (lt_min h0 h1).trans_le
    (FormalMultilinearSeries.le_radius_pi hle)

/-- The state FMS sums to componentwise bivariate evaluation on every closed
box strictly inside the product radius. -/
theorem hasSum_stateFMS
    {a : FirstOrderStateCoeff} {M sx sy rx ry x y : ℝ}
    (h : CKVectorAnalyticEvaluation.VectorGeometricBound
      (fun i m n => a m n i) M sx sy)
    (hrx : 0 ≤ rx) (hry : 0 ≤ ry)
    (hxrate : sx * rx < 1) (hyrate : sy * ry < 1)
    (hx : |x| ≤ rx) (hy : |y| ≤ ry) :
    HasSum (fun k => stateFMS a k (fun _ => (x, y)))
      (fun i => eval (fun m n => a m n i) x y) := by
  rw [Pi.hasSum]
  intro i
  simpa only [stateFMS, FormalMultilinearSeries.pi,
    ContinuousMultilinearMap.pi_apply] using
    hasSum_bivariateFMS (h.component i) hrx hry hxrate hyrate hx hy

/-- The componentwise evaluated state series has `stateFMS a` as an actual
power series at the origin. -/
theorem hasFPowerSeriesAt_stateFMS
    {a : FirstOrderStateCoeff} {M sx sy rx ry : ℝ}
    (h : CKVectorAnalyticEvaluation.VectorGeometricBound
      (fun i m n => a m n i) M sx sy)
    (hrx : 0 < rx) (hry : 0 < ry)
    (hxrate : sx * rx < 1) (hyrate : sy * ry < 1) :
    HasFPowerSeriesAt
      (fun p : ℝ × ℝ => fun i => eval (fun m n => a m n i) p.1 p.2)
      (stateFMS a) 0 := by
  let q := stateFMS a
  have hqpos : 0 < q.radius := radius_stateFMS_pos h
  have hq : HasFPowerSeriesAt q.sum q 0 :=
    ⟨q.radius, q.hasFPowerSeriesOnBall hqpos⟩
  apply hq.congr
  have hopen : IsOpen
      (Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry) :=
    isOpen_Ioo.prod isOpen_Ioo
  have hzero : (0 : ℝ × ℝ) ∈
      (Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry) := by
    simp [hrx, hry]
  filter_upwards [hopen.mem_nhds hzero] with z hz
  have hs := hasSum_stateFMS h hrx.le hry.le hxrate hyrate
    (abs_lt.mpr hz.1).le (abs_lt.mpr hz.2).le
  simpa only [q, FormalMultilinearSeries.sum] using hs.tsum_eq

end

end CKPolarEvaluation
end StressTensor
