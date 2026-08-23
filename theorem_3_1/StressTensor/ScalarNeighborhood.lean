import StressTensor.ScalarFactors
import StressTensor.ScalarDerivatives
import StressTensor.ScalarAnalyticity
import StressTensor.Bounds
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quantitative scalar estimates on `V_q`

This file proves the scalar bounds asserted in (3.19)--(3.20) directly from
membership in the neighborhood `V_q`.  In particular, it discharges the
positivity hypotheses used by the real-power identities elsewhere in the
formalization.
-/

namespace StressTensor

noncomputable section

namespace Params

/-- A denominator-free form of Hölder conjugacy used in the scalar bounds. -/
theorem q_sub_one_mul_p (P : Params) : (P.q - 1) * P.p = P.q := by
  have hholder := P.holder
  field_simp [P.p_pos.ne', P.q_pos.ne'] at hholder
  nlinarith

end Params

namespace InV

variable {P : Params} {t d : ℝ}

/-- On `V_q`, the real-power base is at most one. -/
theorem base_le_one (h : InV P t d) :
    1 + t ^ 2 * d ≤ 1 := by
  have hd : d < 0 := by linarith [h.neg_d_bounds.1]
  have hprod : t ^ 2 * d ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) hd.le
  linarith

/-- The quantitative base bound used below; it is stronger than the `1/2`
bound displayed in (3.19). -/
theorem three_quarters_lt_base (h : InV P t d) :
    (3 : ℝ) / 4 < 1 + t ^ 2 * d := by
  have hrhoSq : P.rho ^ 2 < ((1 : ℝ) / 1024) ^ 2 :=
    (sq_lt_sq₀ P.rho_pos.le (by norm_num)).2 P.rho_lt_one_div_1024
  have hsmall : 4 * P.rho ^ 2 < (1 : ℝ) / 4 := by
    nlinarith
  have hprod := (abs_lt.mp h.abs_t_sq_mul_d_lt).1
  linarith

/-- Positivity of the real-power base on `V_q`. -/
theorem base_pos (h : InV P t d) : 0 < 1 + t ^ 2 * d := by
  linarith [h.three_quarters_lt_base]

/-- The negative exponent in (3.19) makes the power at least one. -/
theorem one_le_base_rpow (h : InV P t d) :
    1 ≤ Real.rpow (1 + t ^ 2 * d) ((P.q - 2) / 2) := by
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos h.base_pos h.base_le_one
    (by linarith [P.q_lt_two])

/-- The first displayed estimate in (3.19). -/
theorem one_half_lt_min_base_rpow (h : InV P t d) :
    (1 : ℝ) / 2 <
      min (1 + t ^ 2 * d)
        (Real.rpow (1 + t ^ 2 * d) ((P.q - 2) / 2)) := by
  apply lt_min
  · linarith [h.three_quarters_lt_base]
  · linarith [h.one_le_base_rpow]

/-- Every affine base appearing in the integral representation of `Ctilde`
stays in the same positive interval. -/
theorem three_quarters_lt_segment_base (h : InV P t d) {tau : ℝ}
    (htau : tau ∈ Set.Icc (0 : ℝ) 1) :
    (3 : ℝ) / 4 < 1 + tau * t ^ 2 * d := by
  have hd : d < 0 := by linarith [h.neg_d_bounds.1]
  have htd : t ^ 2 * d ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) hd.le
  have hcompare : t ^ 2 * d ≤ tau * (t ^ 2 * d) := by
    have hnonneg :=
      mul_nonneg (sub_nonneg.mpr htau.2) (neg_nonneg.mpr htd)
    nlinarith
  have hbase := h.three_quarters_lt_base
  nlinarith

/-- The affine base along the integration segment is at most one. -/
theorem segment_base_le_one (h : InV P t d) {tau : ℝ}
    (htau : tau ∈ Set.Icc (0 : ℝ) 1) :
    1 + tau * t ^ 2 * d ≤ 1 := by
  have hd : d < 0 := by linarith [h.neg_d_bounds.1]
  have htd : t ^ 2 * d ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) hd.le
  have : tau * (t ^ 2 * d) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos htau.1 htd
  nlinarith

/-- Pointwise lower bound for the integrand in the integral representation
of `Ctilde`. -/
theorem one_le_segment_base_rpow (h : InV P t d) {tau : ℝ}
    (htau : tau ∈ Set.Icc (0 : ℝ) 1) :
    1 ≤ Real.rpow (1 + tau * t ^ 2 * d) ((P.q - 2) / 2) := by
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    (by linarith [h.three_quarters_lt_segment_base htau])
    (h.segment_base_le_one htau) (by linarith [P.q_lt_two])

/-- A convenient strict upper bound for the same integral kernel. -/
theorem segment_base_rpow_lt_four_thirds (h : InV P t d) {tau : ℝ}
    (htau : tau ∈ Set.Icc (0 : ℝ) 1) :
    Real.rpow (1 + tau * t ^ 2 * d) ((P.q - 2) / 2) < (4 : ℝ) / 3 := by
  have hbasePos : 0 < 1 + tau * t ^ 2 * d := by
    linarith [h.three_quarters_lt_segment_base htau]
  have hpowInv :
      Real.rpow (1 + tau * t ^ 2 * d) ((P.q - 2) / 2) ≤
        Real.rpow (1 + tau * t ^ 2 * d) (-1 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_ge hbasePos
      (h.segment_base_le_one htau) (by linarith [P.q_pos])
  have hInv : (1 + tau * t ^ 2 * d)⁻¹ < (4 : ℝ) / 3 := by
    rw [inv_lt_iff_one_lt_mul₀ hbasePos]
    nlinarith [h.three_quarters_lt_segment_base htau]
  have hpowInv' :
      Real.rpow (1 + tau * t ^ 2 * d) ((P.q - 2) / 2) ≤
        (1 + tau * t ^ 2 * d)⁻¹ := by
    have heq :
        Real.rpow (1 + tau * t ^ 2 * d) (-1 : ℝ) =
          (1 + tau * t ^ 2 * d)⁻¹ := by
      exact Real.rpow_neg_one (1 + tau * t ^ 2 * d)
    exact hpowInv.trans_eq heq
  exact lt_of_le_of_lt hpowInv' hInv

/-- Bounds for the integral kernel in (3.6), integrated over `[0,1]`. -/
theorem integral_base_rpow_bounds (h : InV P t d) :
    1 ≤
        ∫ tau in (0 : ℝ)..1,
          Real.rpow (1 + tau * t ^ 2 * d) ((P.q - 2) / 2) ∧
      (∫ tau in (0 : ℝ)..1,
          Real.rpow (1 + tau * t ^ 2 * d) ((P.q - 2) / 2)) ≤ (4 : ℝ) / 3 := by
  let f : ℝ → ℝ := fun tau =>
    Real.rpow (1 + tau * t ^ 2 * d) ((P.q - 2) / 2)
  have hcont : ContinuousOn f (Set.uIcc (0 : ℝ) 1) := by
    intro tau htau
    have htauIcc : tau ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le zero_le_one] using htau
    have hbaseCont : ContinuousAt (fun s : ℝ => 1 + s * t ^ 2 * d) tau := by
      fun_prop
    exact (hbaseCont.rpow_const
      (Or.inl (ne_of_gt (by
        linarith [h.three_quarters_lt_segment_base htauIcc])))).continuousWithinAt
  have hf : IntervalIntegrable f MeasureTheory.volume (0 : ℝ) 1 :=
    hcont.intervalIntegrable
  constructor
  · have hmono := intervalIntegral.integral_mono_on
      (f := fun _ : ℝ => (1 : ℝ)) (g := f) zero_le_one
      intervalIntegrable_const hf
      (fun tau htau => h.one_le_segment_base_rpow htau)
    simpa [f] using hmono
  · have hmono := intervalIntegral.integral_mono_on
      (f := f) (g := fun _ : ℝ => (4 : ℝ) / 3) zero_le_one
      hf intervalIntegrable_const
      (fun tau htau => le_of_lt (h.segment_base_rpow_lt_four_thirds htau))
    simpa [f] using hmono

/-- On `V_q`, the integral and removable-quotient presentations of `Ctilde`
agree, including at `t = 0`. -/
theorem CtildeIntegral_eq_Ctilde (h : InV P t d) :
    CtildeIntegral P t d = Ctilde P t d := by
  by_cases ht : t = 0
  · subst t
    simp
  · exact CtildeIntegral_eq_Ctilde_of_ne P t d ht
      (fun tau htau => by
        linarith [h.three_quarters_lt_segment_base htau])

/-- The two-sided `Ctilde` estimate in (3.19). -/
theorem Ctilde_bounds (h : InV P t d) :
    (1 : ℝ) / 4 < Ctilde P t d ∧ Ctilde P t d < 4 := by
  let I : ℝ :=
    ∫ tau in (0 : ℝ)..1,
      Real.rpow (1 + tau * t ^ 2 * d) ((P.q - 2) / 2)
  let A : ℝ := -(P.q * d / 2)
  have hI : 1 ≤ I ∧ I ≤ (4 : ℝ) / 3 := by
    simpa only [I] using h.integral_base_rpow_bounds
  have hIpos : 0 < I := lt_of_lt_of_le zero_lt_one hI.1
  have hApos : 0 < A := by
    dsimp only [A]
    have hd : d < 0 := by linarith [h.neg_d_bounds.1]
    have hprod : 0 < P.q * (-d) := mul_pos P.q_pos (neg_pos.mpr hd)
    nlinarith
  have hA_lower : (1 : ℝ) / 2 < A := by
    have hcross :
        0 < (P.q - 1) * ((-d) - 1) :=
      mul_pos (sub_pos.mpr P.one_lt_q)
        (sub_pos.mpr h.neg_d_bounds.1)
    dsimp only [A]
    nlinarith [P.one_lt_q, h.neg_d_bounds.1, hcross]
  have hnegd_lt_three : -d < (3 : ℝ) := by
    have hd := (abs_lt.mp h.2).1
    linarith [P.rho_lt_one_div_1024]
  have hA_upper : A < 3 := by
    have hfirst : 0 < P.q * (3 - (-d)) :=
      mul_pos P.q_pos (sub_pos.mpr hnegd_lt_three)
    have hsecond : 0 < 3 * (2 - P.q) :=
      mul_pos (by norm_num) (sub_pos.mpr P.q_lt_two)
    dsimp only [A]
    nlinarith [P.q_lt_two, hnegd_lt_three, hfirst, hsecond]
  have hCeq : Ctilde P t d = A * I := by
    rw [← h.CtildeIntegral_eq_Ctilde]
    rfl
  rw [hCeq]
  constructor
  · have hA_le_prod : A ≤ A * I := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hI.1 hApos.le
    linarith
  · have hprod_lt : A * I < 3 * I :=
      mul_lt_mul_of_pos_right hA_upper hIpos
    have hthreeI : 3 * I ≤ 4 := by
      nlinarith [hI.2]
    exact lt_of_lt_of_le hprod_lt hthreeI

/-- Positivity of `Ctilde` follows automatically from `V_q`. -/
theorem Ctilde_pos (h : InV P t d) : 0 < Ctilde P t d := by
  linarith [h.Ctilde_bounds.1]

/-- The lower bound for `Stilde` in (3.19). -/
theorem one_eighth_le_Stilde (h : InV P t d) :
    (1 : ℝ) / 8 ≤ Stilde P t d := by
  have hpow :
      1 ≤ Real.rpow (1 + t ^ 2 * d) ((P.q - 2) / 2) :=
    h.one_le_base_rpow
  have hinvpPos : 0 < 1 / P.p := div_pos zero_lt_one P.p_pos
  have hinvpLe : 1 / P.p ≤ 1 := by
    apply (div_le_iff₀ P.p_pos).2
    linarith [P.two_lt_p]
  have hCpowPos : 0 < Real.rpow (Ctilde P t d) (1 / P.p) :=
    Real.rpow_pos_of_pos h.Ctilde_pos _
  have hCpowLe : Real.rpow (Ctilde P t d) (1 / P.p) ≤ 4 := by
    calc
      Real.rpow (Ctilde P t d) (1 / P.p) ≤
          Real.rpow 4 (1 / P.p) :=
        Real.rpow_le_rpow h.Ctilde_pos.le h.Ctilde_bounds.2.le hinvpPos.le
      _ ≤ Real.rpow 4 1 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hinvpLe
      _ = 4 := Real.rpow_one 4
  have hquarter :
      (1 : ℝ) / 4 ≤
        Real.rpow (1 + t ^ 2 * d) ((P.q - 2) / 2) /
          Real.rpow (Ctilde P t d) (1 / P.p) := by
    apply (le_div_iff₀ hCpowPos).2
    calc
      (1 : ℝ) / 4 * Real.rpow (Ctilde P t d) (1 / P.p) ≤ 1 := by
        nlinarith
      _ ≤ Real.rpow (1 + t ^ 2 * d) ((P.q - 2) / 2) := hpow
  simpa only [Stilde] using le_trans (by norm_num : (1 : ℝ) / 8 ≤ 1 / 4) hquarter

/-- The logarithmic derivative lower bound in (3.20), now derived entirely
from membership in `V_q`. -/
theorem stildeDLogRate_ge_q_sub_one_div_32 (h : InV P t d) :
    (P.q - 1) / 32 ≤ stildeDLogRate P t d := by
  let base : ℝ := 1 + t ^ 2 * d
  let ratio : ℝ := t ^ 2 / base
  let powD : ℝ := Real.rpow base (-1 + P.q / 2)
  have hbasePos : 0 < base := by simpa only [base] using h.base_pos
  have htSq : t ^ 2 < P.rho ^ 2 := by
    apply (sq_lt_sq).2
    simpa [abs_of_pos P.rho_pos] using h.1
  have hratioNonneg : 0 ≤ ratio := by
    exact div_nonneg (sq_nonneg t) hbasePos.le
  have hratioLt : ratio < 2 * P.rho ^ 2 := by
    apply (div_lt_iff₀ hbasePos).2
    have hone : 1 < 2 * base := by
      dsimp only [base]
      linarith [h.three_quarters_lt_base]
    have hscaled : P.rho ^ 2 < P.rho ^ 2 * (2 * base) := by
      have := mul_lt_mul_of_pos_left hone (sq_pos_of_pos P.rho_pos)
      nlinarith
    exact lt_trans htSq (by nlinarith [hscaled])
  have hratioLe : ratio ≤ 2 * P.rho := by
    have hrhoSqLt : P.rho ^ 2 < P.rho := by
      nlinarith [P.rho_pos, P.rho_lt_one]
    linarith
  have hnegative :
      -(2 - P.q) * P.rho ≤ ((P.q - 2) / 2) * ratio := by
    have hmul := mul_le_mul_of_nonneg_left hratioLe
      (show 0 ≤ (2 - P.q) / 2 by linarith [P.q_lt_two])
    nlinarith
  have hpowD : 1 ≤ powD := by
    have hexp : -1 + P.q / 2 = (P.q - 2) / 2 := by ring
    dsimp only [powD, base]
    rw [hexp]
    exact h.one_le_base_rpow
  have hdenPos : 0 < 2 * P.p * Ctilde P t d := by
    exact mul_pos (mul_pos (by norm_num) P.p_pos) h.Ctilde_pos
  have hpositive :
      (P.q - 1) / 8 ≤
        P.q * powD / (2 * P.p * Ctilde P t d) := by
    apply (le_div_iff₀ hdenPos).2
    calc
      (P.q - 1) / 8 * (2 * P.p * Ctilde P t d) =
          ((P.q - 1) * P.p) * Ctilde P t d / 4 := by ring
      _ = P.q * Ctilde P t d / 4 := by rw [P.q_sub_one_mul_p]
      _ ≤ P.q := by
        have hmul :=
          mul_le_mul_of_nonneg_left h.Ctilde_bounds.2.le P.q_pos.le
        nlinarith
      _ ≤ P.q * powD :=
        by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hpowD P.q_pos.le
  have hpenalty :
      (2 - P.q) * P.rho ≤ (P.q - 1) / 1024 := by
    have hfrac : (2 - P.q) / P.q ≤ 1 := by
      apply (div_le_one P.q_pos).2
      linarith [P.one_lt_q]
    have hscale : 0 ≤ (P.q - 1) / 1024 := by
      exact div_nonneg (sub_nonneg.mpr P.one_lt_q.le) (by norm_num)
    rw [Params.rho]
    calc
      (2 - P.q) * ((P.q - 1) / ((2 : ℝ) ^ 10 * P.q)) =
          ((P.q - 1) / 1024) * ((2 - P.q) / P.q) := by
        field_simp [P.q_pos.ne']
        ring
      _ ≤ ((P.q - 1) / 1024) * 1 :=
        mul_le_mul_of_nonneg_left hfrac hscale
      _ = (P.q - 1) / 1024 := by ring
  have htarget :
      (P.q - 1) / 32 ≤
        -(2 - P.q) * P.rho + (P.q - 1) / 8 := by
    nlinarith [P.one_lt_q, hpenalty]
  rw [stildeDLogRate]
  have hsum := add_le_add hnegative hpositive
  dsimp only [ratio, base, powD] at hsum
  simpa only [mul_div_assoc] using le_trans htarget hsum

/-- The lower bound in (3.20), stated for the actual `d` derivative of
`Stilde`. -/
theorem deriv_Stilde_d_div_ge_q_sub_one_div_32 (h : InV P t d) :
    (P.q - 1) / 32 ≤
      deriv (fun d' => Stilde P t d') d / Stilde P t d := by
  rw [deriv_Stilde_d_div P t d h.base_pos h.Ctilde_pos]
  exact h.stildeDLogRate_ge_q_sub_one_div_32

/-! ## Analyticity on the full scalar neighborhood -/

/-- The smallness condition defining `V_q` lies strictly inside the
binomial-series domain `|t²d| < 1`. -/
theorem abs_t_sq_mul_d_lt_one (h : InV P t d) :
    |t ^ 2 * d| < 1 := by
  have hrho : 4 * P.rho ^ 2 < 1 := by
    nlinarith [P.rho_pos, P.rho_lt_one_div_1024]
  exact h.abs_t_sq_mul_d_lt.trans hrho

/-- The continued deficit factor is analytic at every point of `V_q`. -/
theorem analyticAt_Ctilde (h : InV P t d) :
    AnalyticAt ℝ (fun z : ℝ × ℝ => Ctilde P z.1 z.2) (t, d) :=
  analyticAt_Ctilde_of_abs_sq_mul_lt_one P h.abs_t_sq_mul_d_lt_one

/-- The continued stress factor is analytic at every point of `V_q`. -/
theorem analyticAt_Stilde (h : InV P t d) :
    AnalyticAt ℝ (fun z : ℝ × ℝ => Stilde P z.1 z.2) (t, d) :=
  analyticAt_Stilde_of_pos P h.abs_t_sq_mul_d_lt_one h.base_pos h.Ctilde_pos

end InV

/-- `Ctilde` is analytic on a neighborhood of every point of `V_q`. -/
theorem analyticOnNhd_Ctilde_inV (P : Params) :
    AnalyticOnNhd ℝ (fun z : ℝ × ℝ => Ctilde P z.1 z.2)
      {z : ℝ × ℝ | InV P z.1 z.2} := by
  intro z hz
  exact hz.analyticAt_Ctilde

/-- `Stilde` is analytic on a neighborhood of every point of `V_q`, as
claimed before (3.20). -/
theorem analyticOnNhd_Stilde_inV (P : Params) :
    AnalyticOnNhd ℝ (fun z : ℝ × ℝ => Stilde P z.1 z.2)
      {z : ℝ × ℝ | InV P z.1 z.2} := by
  intro z hz
  exact hz.analyticAt_Stilde

end

end StressTensor
