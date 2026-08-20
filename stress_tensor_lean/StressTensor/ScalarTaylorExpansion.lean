import Mathlib.Analysis.Asymptotics.Lemmas
import StressTensor.ScalarAnalyticity

/-!
# The explicit Taylor expansion of the continued scalar factor

This file extracts the two displayed Taylor coefficients of `Ctilde` from
the full binomial formal-power-series germ already used to prove its
analyticity.  It also packages the remaining analytic tail and proves the
literal local big-O estimate appearing in the manuscript.
-/

namespace StressTensor

open Asymptotics Filter

noncomputable section

/-- The first divided slope in the binomial expansion of `deficitPower`. -/
def deficitPowerFirstSlope (P : Params) : ℝ → ℝ :=
  dslope (deficitPower P) 0

/-- The second divided slope in the binomial expansion of `deficitPower`. -/
def deficitPowerSecondSlope (P : Params) : ℝ → ℝ :=
  dslope (deficitPowerFirstSlope P) 0

/-- The third divided slope, which is the analytic Taylor tail used below. -/
def deficitPowerThirdSlope (P : Params) : ℝ → ℝ :=
  dslope (deficitPowerSecondSlope P) 0

/-- The analytic tail in the displayed Taylor expansion of `Ctilde`. -/
def CtildeTaylorTail (P : Params) (s : ℝ) : ℝ :=
  -deficitPowerThirdSlope P s

/-- The difference between `Ctilde` and the two terms displayed in the manuscript. -/
def CtildeTaylorRemainder (P : Params) (t d : ℝ) : ℝ :=
  Ctilde P t d + P.q * d / 2 + P.q * (P.q - 2) / 8 * t ^ 2 * d ^ 2

private theorem deficitPowerFirstSlope_zero (P : Params) :
    deficitPowerFirstSlope P 0 = P.q / 2 := by
  simp [deficitPowerFirstSlope, hasDerivAt_deficitPower_zero P |>.deriv]

private theorem deficitPowerSecondSlope_zero (P : Params) :
    deficitPowerSecondSlope P 0 = P.q * (P.q - 2) / 8 := by
  let a : ℝ := P.q / 2
  have hp := Real.one_add_rpow_hasFPowerSeriesAt_zero (a := a)
  change HasFPowerSeriesAt (deficitPower P) (binomialSeries ℝ a) 0 at hp
  have hc :=
    (hp.has_fpower_series_iterate_dslope_fslope 2).coeff_zero
      (fun _ : Fin 0 => (1 : ℝ))
  change
    ((FormalMultilinearSeries.fslope^[2]) (binomialSeries ℝ a)) 0
        (fun _ : Fin 0 => (1 : ℝ)) =
      ((Function.swap dslope 0)^[2] (deficitPower P)) 0 at hc
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    FormalMultilinearSeries.coeff_iterate_fslope] at hc
  have hprod : (∏ _ : Fin 0, (1 : ℝ)) = 1 := by simp
  rw [hprod, one_smul, zero_add] at hc
  have hcoeff : (binomialSeries ℝ a).coeff 2 = Ring.choose a 2 := by
    unfold FormalMultilinearSeries.coeff
    rw [binomialSeries_apply]
    simp
  rw [hcoeff] at hc
  change Ring.choose a 2 = deficitPowerSecondSlope P 0 at hc
  rw [← hc]
  dsimp [a]
  norm_num [Ring.choose_eq_smul, descPochhammer_succ_right,
    Polynomial.smeval_mul, Polynomial.smeval_natCast]
  ring

private theorem firstSlope_expansion (P : Params) (s : ℝ) :
    deficitPowerFirstSlope P s =
      P.q / 2 + s * deficitPowerSecondSlope P s := by
  have h := sub_smul_dslope (deficitPowerFirstSlope P) 0 s
  simp only [sub_zero, smul_eq_mul] at h
  change s * deficitPowerSecondSlope P s =
    deficitPowerFirstSlope P s - deficitPowerFirstSlope P 0 at h
  rw [deficitPowerFirstSlope_zero P] at h
  linarith

private theorem secondSlope_expansion (P : Params) (s : ℝ) :
    deficitPowerSecondSlope P s =
      P.q * (P.q - 2) / 8 + s * deficitPowerThirdSlope P s := by
  have h := sub_smul_dslope (deficitPowerSecondSlope P) 0 s
  simp only [sub_zero, smul_eq_mul] at h
  change s * deficitPowerThirdSlope P s =
    deficitPowerSecondSlope P s - deficitPowerSecondSlope P 0 at h
  rw [deficitPowerSecondSlope_zero P] at h
  linarith

/-- Exact form of the manuscript's truncated Taylor display.  The remainder
is not merely bounded: it factors globally through the third divided slope. -/
theorem Ctilde_eq_truncated_add_tail (P : Params) (t d : ℝ) :
    Ctilde P t d =
      -(P.q * d) / 2 - P.q * (P.q - 2) / 8 * t ^ 2 * d ^ 2 +
        t ^ 4 * d ^ 3 * CtildeTaylorTail P (t ^ 2 * d) := by
  rw [Ctilde_eq_CtildeSlope]
  simp only [CtildeSlope]
  change -d * deficitPowerFirstSlope P (t ^ 2 * d) = _
  rw [firstSlope_expansion, secondSlope_expansion]
  simp only [CtildeTaylorTail]
  ring

/-- The named Taylor remainder equals the explicit fourth-order tail factor. -/
theorem CtildeTaylorRemainder_eq (P : Params) (t d : ℝ) :
    CtildeTaylorRemainder P t d =
      t ^ 4 * d ^ 3 * CtildeTaylorTail P (t ^ 2 * d) := by
  rw [CtildeTaylorRemainder, Ctilde_eq_truncated_add_tail]
  ring

/-- The tail in the exact factorization is analytic at the origin. -/
theorem analyticAt_CtildeTaylorTail_zero (P : Params) :
    AnalyticAt ℝ (CtildeTaylorTail P) 0 := by
  have hp := Real.one_add_rpow_hasFPowerSeriesAt_zero (a := P.q / 2)
  change HasFPowerSeriesAt
    (deficitPower P) (binomialSeries ℝ (P.q / 2)) 0 at hp
  have hfirst := hp.has_fpower_series_dslope_fslope
  have hsecond := hfirst.has_fpower_series_dslope_fslope
  have hthird := hsecond.has_fpower_series_dslope_fslope
  have hthirdAnalytic : AnalyticAt ℝ (deficitPowerThirdSlope P) 0 := by
    simpa [deficitPowerThirdSlope, deficitPowerSecondSlope,
      deficitPowerFirstSlope] using hthird.analyticAt
  change AnalyticAt ℝ (-deficitPowerThirdSlope P) 0
  exact hthirdAnalytic.neg

/-- Literal two-variable interpretation of the manuscript notation
`g(t,d) = O(t⁴d³)`: for every fixed `d₀`, the named remainder has this
big-O bound as `(t,d) → (0,d₀)`. -/
theorem CtildeTaylorRemainder_isBigO (P : Params) (d₀ : ℝ) :
    (fun z : ℝ × ℝ => CtildeTaylorRemainder P z.1 z.2) =O[nhds (0, d₀)]
      (fun z : ℝ × ℝ => z.1 ^ 4 * z.2 ^ 3) := by
  have hargContinuous :
      ContinuousAt (fun z : ℝ × ℝ => z.1 ^ 2 * z.2) (0, d₀) :=
    (continuousAt_fst.pow 2).mul continuousAt_snd
  have harg : Tendsto (fun z : ℝ × ℝ => z.1 ^ 2 * z.2) (nhds (0, d₀)) (nhds 0) := by
    change Tendsto (fun z : ℝ × ℝ => z.1 ^ 2 * z.2) (nhds (0, d₀))
      (nhds ((0 : ℝ) ^ 2 * d₀)) at hargContinuous
    norm_num at hargContinuous
    exact hargContinuous
  have htailAtZero : Tendsto (CtildeTaylorTail P) (nhds 0)
      (nhds (CtildeTaylorTail P 0)) :=
    (analyticAt_CtildeTaylorTail_zero P).continuousAt
  have htail : Tendsto
      (fun z : ℝ × ℝ => CtildeTaylorTail P (z.1 ^ 2 * z.2))
      (nhds (0, d₀)) (nhds (CtildeTaylorTail P 0)) :=
    htailAtZero.comp harg
  have hbounded :
      (fun z : ℝ × ℝ => CtildeTaylorTail P (z.1 ^ 2 * z.2)) =O[nhds (0, d₀)]
        (fun _ : ℝ × ℝ => (1 : ℝ)) :=
    htail.isBigO_one ℝ
  have hfactor :
      (fun z : ℝ × ℝ => z.1 ^ 4 * z.2 ^ 3) =O[nhds (0, d₀)]
        (fun z : ℝ × ℝ => z.1 ^ 4 * z.2 ^ 3) :=
    isBigO_refl _ _
  exact (hfactor.mul hbounded).congr
    (fun z => (CtildeTaylorRemainder_eq P z.1 z.2).symm)
    (fun z => by simp)

end

end StressTensor
