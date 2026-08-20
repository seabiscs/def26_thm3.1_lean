import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Exponential
import StressTensor.ScalarDerivatives

/-!
# Analyticity of the continued scalar factors

The removable quotient defining `Ctilde` is represented as the analytic
divided slope of `s ↦ (1+s)^(q/2)`.  This removes the piecewise presentation
at `t = 0` and supplies the local analyticity needed at `(0,-2)`.
-/

namespace StressTensor

noncomputable section

/-- The one-variable real-power function whose divided slope occurs in `Ctilde`. -/
def deficitPower (P : Params) (s : ℝ) : ℝ :=
  Real.rpow (1 + s) (P.q / 2)

/-- An analytic divided-slope presentation of the continued quotient. -/
def CtildeSlope (P : Params) (t d : ℝ) : ℝ :=
  -d * dslope (deficitPower P) 0 (t ^ 2 * d)

/-- A positive analytic real-valued function remains analytic after taking a
fixed real power. -/
theorem analyticAt_rpow_of_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : AnalyticAt ℝ f x) (hpos : 0 < f x) (a : ℝ) :
    AnalyticAt ℝ (fun z => Real.rpow (f z) a) x := by
  have hinner : AnalyticAt ℝ (fun z => a * Real.log (f z)) x := by
    have hscaled := ((analyticAt_log hpos).comp hf).const_smul (c := a)
    convert hscaled using 1
    funext z
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
  have hexp : AnalyticAt ℝ (fun z => Real.exp (a * Real.log (f z))) x := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.exp_analytic _).comp hinner
  apply hexp.congr
  have hev : ∀ᶠ z in nhds x, 0 < f z :=
    continuousAt_const.eventually_lt hf.continuousAt hpos
  filter_upwards [hev] with z hz
  simpa only [Real.rpow_eq_pow, mul_comm] using (Real.rpow_def_of_pos hz a).symm

theorem hasDerivAt_deficitPower_zero (P : Params) :
    HasDerivAt (deficitPower P) (P.q / 2) 0 := by
  have hbase : HasDerivAt (fun s : ℝ => 1 + s) 1 0 := by
    simpa using (hasDerivAt_id' (𝕜 := ℝ) 0).const_add (1 : ℝ)
  change HasDerivAt (fun s : ℝ => Real.rpow (1 + s) (P.q / 2)) (P.q / 2) 0
  simpa using hbase.rpow_const (Or.inl (by norm_num : (1 + (0 : ℝ)) ≠ 0))

/-- The piecewise quotient agrees everywhere with its divided-slope continuation. -/
theorem Ctilde_eq_CtildeSlope (P : Params) (t d : ℝ) :
    Ctilde P t d = CtildeSlope P t d := by
  by_cases ht : t = 0
  · subst t
    simp [CtildeSlope, hasDerivAt_deficitPower_zero P |>.deriv]
    ring_nf
  · rw [Ctilde_of_ne_zero P ht]
    by_cases hd : d = 0
    · simp [CtildeSlope, hd]
    · have hs : t ^ 2 * d ≠ 0 := mul_ne_zero (pow_ne_zero 2 ht) hd
      have hds := sub_smul_dslope (deficitPower P) 0 (t ^ 2 * d)
      simp only [sub_zero, smul_eq_mul, deficitPower] at hds
      rw [CtildeSlope, div_eq_iff (pow_ne_zero 2 ht)]
      calc
        1 - Real.rpow (1 + t ^ 2 * d) (P.q / 2) =
            -(t ^ 2 * d * dslope (deficitPower P) 0 (t ^ 2 * d)) := by
              rw [hds]
              simp
        _ = (-d * dslope (deficitPower P) 0 (t ^ 2 * d)) * t ^ 2 := by ring

/-- The divided slope is analytic at its removable point. -/
theorem analyticAt_dslope_deficitPower_zero (P : Params) :
    AnalyticAt ℝ (dslope (deficitPower P) 0) 0 := by
  have hp := Real.one_add_rpow_hasFPowerSeriesAt_zero (a := P.q / 2)
  change HasFPowerSeriesAt (deficitPower P) (binomialSeries ℝ (P.q / 2)) 0 at hp
  exact hp.has_fpower_series_dslope_fslope.analyticAt

/-- The divided-slope continuation is analytic at every point whose
real-power base remains positive. -/
theorem analyticAt_dslope_deficitPower_of_abs_lt_one
    (P : Params) {s : ℝ} (hs : |s| < 1) :
    AnalyticAt ℝ (dslope (deficitPower P) 0) s := by
  by_cases hs0 : s = 0
  · simpa [hs0] using analyticAt_dslope_deficitPower_zero P
  · have hbase : AnalyticAt ℝ (fun u : ℝ => 1 + u) s :=
      analyticAt_const.add analyticAt_id
    have hbasePos : 0 < 1 + s := by
      have := (abs_lt.mp hs).1
      linarith
    have hf : AnalyticAt ℝ (deficitPower P) s := by
      exact analyticAt_rpow_of_pos hbase hbasePos (P.q / 2)
    have hquot : AnalyticAt ℝ
        (fun u => (deficitPower P u - deficitPower P 0) / (u - 0)) s := by
      convert! (hf.sub analyticAt_const).div
        (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs0) using 1
    apply hquot.congr
    filter_upwards [dslope_eventuallyEq_slope_of_ne (deficitPower P) hs0] with u hu
    simpa only [slope_def_field] using hu.symm

/-- `Ctilde` is analytic at every `(t,d)` with `|t²d| < 1`, including the
removable axis `t = 0`. -/
theorem analyticAt_Ctilde_of_abs_sq_mul_lt_one
    (P : Params) {t d : ℝ} (h : |t ^ 2 * d| < 1) :
    AnalyticAt ℝ (fun z : ℝ × ℝ => Ctilde P z.1 z.2) (t, d) := by
  have harg : AnalyticAt ℝ (fun z : ℝ × ℝ => z.1 ^ 2 * z.2) (t, d) :=
    (analyticAt_fst.pow 2).mul analyticAt_snd
  have hds : AnalyticAt ℝ
      (fun z : ℝ × ℝ => dslope (deficitPower P) 0 (z.1 ^ 2 * z.2)) (t, d) :=
    (analyticAt_dslope_deficitPower_of_abs_lt_one P h).comp_of_eq harg rfl
  have hslope : AnalyticAt ℝ
      (fun z : ℝ × ℝ => -z.2 * dslope (deficitPower P) 0 (z.1 ^ 2 * z.2)) (t, d) :=
    analyticAt_snd.neg.mul hds
  apply hslope.congr
  exact Filter.Eventually.of_forall fun z => by
    simpa only [CtildeSlope] using (Ctilde_eq_CtildeSlope P z.1 z.2).symm

/-- `Ctilde`, viewed as a function of `(t,d)`, is analytic at `(0,-2)`. -/
theorem analyticAt_Ctilde_origin (P : Params) :
    AnalyticAt ℝ (fun z : ℝ × ℝ => Ctilde P z.1 z.2) (0, -2) := by
  have harg : AnalyticAt ℝ (fun z : ℝ × ℝ => z.1 ^ 2 * z.2) (0, -2) := by
    exact (analyticAt_fst.pow 2).mul analyticAt_snd
  have hds : AnalyticAt ℝ
      (fun z : ℝ × ℝ => dslope (deficitPower P) 0 (z.1 ^ 2 * z.2)) (0, -2) :=
    (analyticAt_dslope_deficitPower_zero P).comp_of_eq harg (by norm_num)
  have hslope : AnalyticAt ℝ
      (fun z : ℝ × ℝ => -z.2 * dslope (deficitPower P) 0 (z.1 ^ 2 * z.2)) (0, -2) := by
    exact analyticAt_snd.neg.mul hds
  apply hslope.congr
  exact Filter.Eventually.of_forall fun z => by
    simpa only [CtildeSlope] using (Ctilde_eq_CtildeSlope P z.1 z.2).symm

/-- `Stilde`, viewed as a function of `(t,d)`, is analytic at `(0,-2)`. -/
theorem analyticAt_Stilde_origin (P : Params) :
    AnalyticAt ℝ (fun z : ℝ × ℝ => Stilde P z.1 z.2) (0, -2) := by
  have harg : AnalyticAt ℝ (fun z : ℝ × ℝ => z.1 ^ 2 * z.2) (0, -2) :=
    (analyticAt_fst.pow 2).mul analyticAt_snd
  have hbase : AnalyticAt ℝ (fun z : ℝ × ℝ => 1 + z.1 ^ 2 * z.2) (0, -2) :=
    analyticAt_const.add harg
  have hnum : AnalyticAt ℝ
      (fun z : ℝ × ℝ => Real.rpow (1 + z.1 ^ 2 * z.2) ((P.q - 2) / 2)) (0, -2) :=
    analyticAt_rpow_of_pos hbase (by norm_num) ((P.q - 2) / 2)
  have hC := analyticAt_Ctilde_origin P
  have hden : AnalyticAt ℝ
      (fun z : ℝ × ℝ => Real.rpow (Ctilde P z.1 z.2) (1 / P.p)) (0, -2) := by
    apply analyticAt_rpow_of_pos hC
    simpa using Ctilde_zero_neg_two_pos P
  have hden_ne : Real.rpow (Ctilde P (0 : ℝ) (-2)) (1 / P.p) ≠ 0 :=
    (Real.rpow_pos_of_pos (Ctilde_zero_neg_two_pos P) (1 / P.p)).ne'
  convert! hnum.div hden hden_ne using 1

/-- `Stilde` is analytic wherever the real-power base and `Ctilde` are
positive and `|t²d| < 1`. -/
theorem analyticAt_Stilde_of_pos
    (P : Params) {t d : ℝ} (hsmall : |t ^ 2 * d| < 1)
    (hbase : 0 < 1 + t ^ 2 * d) (hC : 0 < Ctilde P t d) :
    AnalyticAt ℝ (fun z : ℝ × ℝ => Stilde P z.1 z.2) (t, d) := by
  have harg : AnalyticAt ℝ (fun z : ℝ × ℝ => z.1 ^ 2 * z.2) (t, d) :=
    (analyticAt_fst.pow 2).mul analyticAt_snd
  have hbaseAnalytic : AnalyticAt ℝ
      (fun z : ℝ × ℝ => 1 + z.1 ^ 2 * z.2) (t, d) :=
    analyticAt_const.add harg
  have hnum : AnalyticAt ℝ
      (fun z : ℝ × ℝ => Real.rpow (1 + z.1 ^ 2 * z.2) ((P.q - 2) / 2))
      (t, d) :=
    analyticAt_rpow_of_pos hbaseAnalytic hbase ((P.q - 2) / 2)
  have hCAnalytic := analyticAt_Ctilde_of_abs_sq_mul_lt_one P hsmall
  have hden : AnalyticAt ℝ
      (fun z : ℝ × ℝ => Real.rpow (Ctilde P z.1 z.2) (1 / P.p)) (t, d) :=
    analyticAt_rpow_of_pos hCAnalytic hC (1 / P.p)
  have hden_ne : Real.rpow (Ctilde P t d) (1 / P.p) ≠ 0 :=
    (Real.rpow_pos_of_pos hC (1 / P.p)).ne'
  convert! hnum.div hden hden_ne using 1

end

end StressTensor
