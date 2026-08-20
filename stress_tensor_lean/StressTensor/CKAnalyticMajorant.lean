import StressTensor.QuasilinearNormalForm

/-!
# Quantitative local series data for the CK coefficients

Mathlib's predicate `AnalyticAt` contains a convergent formal multilinear
series, but it deliberately hides both the series and its convergence ball.
This file packages the quantitative data needed by a coefficient-majorant
argument: a positive finite radius, convergence on that ball, and a geometric
operator-norm bound for every homogeneous coefficient.

The construction is completely general.  The final section applies it to the
normal-form right-hand side and to the three analytic factors in the shifted
zero-Cauchy-data equation.  It does not assert convergence of the recursively
defined CK solution series.
-/

namespace StressTensor

noncomputable section

open NNReal ENNReal

/-! ## A reusable quantitative form of local analyticity -/

section General

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Explicit local power-series data together with a geometric bound on the
operator norms of its homogeneous coefficients.  The radius is an `NNReal`
so that it can be used directly in ordinary real inequalities; it coerces to
`ENNReal` in the convergence-ball statement. -/
structure LocalAnalyticMajorant (f : E → F) (x : E) where
  series : FormalMultilinearSeries ℝ E F
  radius : ℝ≥0
  coefficientBound : ℝ
  radius_pos : 0 < radius
  coefficientBound_pos : 0 < coefficientBound
  radius_lt_seriesRadius : (radius : ℝ≥0∞) < series.radius
  hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall f series x (radius : ℝ≥0∞)
  coeff_norm_le : ∀ n : ℕ,
    ‖series n‖ ≤ coefficientBound / (radius : ℝ) ^ n

namespace LocalAnalyticMajorant

variable {f : E → F} {x : E}

/-- The packaged radius is positive as an ordinary real number. -/
theorem radius_real_pos (M : LocalAnalyticMajorant f x) :
    0 < (M.radius : ℝ) := by
  exact_mod_cast M.radius_pos

/-- The homogeneous coefficient norms are summable at every strictly smaller
radius.  This is the weighted summability input normally used in a CK
majorant argument. -/
theorem summable_coeff_norm (M : LocalAnalyticMajorant f x)
    {s : ℝ≥0} (hs : s < M.radius) :
    Summable fun n : ℕ => ‖M.series n‖ * (s : ℝ) ^ n := by
  apply M.series.summable_norm_mul_pow
  exact (ENNReal.coe_lt_coe.2 hs).trans M.radius_lt_seriesRadius

/-- The packaged series sums to the function at every displacement in its
open convergence ball. -/
theorem hasSum (M : LocalAnalyticMajorant f x) {h : E}
    (hh : h ∈ Metric.eball (0 : E) (M.radius : ℝ≥0∞)) :
    HasSum (fun n : ℕ => M.series n fun _ : Fin n => h) (f (x + h)) :=
  M.hasFPowerSeriesOnBall.hasSum hh

/-- Pointwise multilinear coefficients inherit the geometric operator-norm
bound. -/
theorem coeff_apply_le (M : LocalAnalyticMajorant f x) (n : ℕ)
    (z : Fin n → E) :
    ‖M.series n z‖ ≤
      (M.coefficientBound / (M.radius : ℝ) ^ n) * ∏ i, ‖z i‖ := by
  exact (M.series n).le_of_opNorm_le (M.coeff_norm_le n) z

/-- Diagonal evaluation gives the scalar geometric majorant which is used
when estimating the Taylor series on a norm ball. -/
theorem coeff_diag_le (M : LocalAnalyticMajorant f x) (n : ℕ) (h : E) :
    ‖M.series n (fun _ : Fin n => h)‖ ≤
      M.coefficientBound * (‖h‖ / (M.radius : ℝ)) ^ n := by
  calc
    ‖M.series n (fun _ : Fin n => h)‖
        ≤ (M.coefficientBound / (M.radius : ℝ) ^ n) *
            ∏ _i : Fin n, ‖h‖ := M.coeff_apply_le n _
    _ = M.coefficientBound * (‖h‖ / (M.radius : ℝ)) ^ n := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [div_pow]
      ring

/-- Forgetting the quantitative data recovers ordinary analyticity. -/
theorem analyticAt (M : LocalAnalyticMajorant f x) : AnalyticAt ℝ f x :=
  M.hasFPowerSeriesOnBall.analyticAt

end LocalAnalyticMajorant

/-- Every analytic germ admits a positive finite ball and a geometric bound
on the operator norms of all homogeneous Taylor coefficients. -/
theorem exists_localAnalyticMajorant_of_analyticAt
    {f : E → F} {x : E} (hf : AnalyticAt ℝ f x) :
    Nonempty (LocalAnalyticMajorant f x) := by
  rcases hf with ⟨p, R, hR⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hR.r_pos with ⟨r, hr0, hrR⟩
  have hr0' : (0 : ℝ≥0) < r := by exact_mod_cast hr0
  have hrp : (r : ℝ≥0∞) < p.radius := hrR.trans_le hR.r_le
  have hrreal : 0 < (r : ℝ) := by exact_mod_cast hr0'
  rcases p.norm_le_div_pow_of_pos_of_lt_radius hrreal hrp with
    ⟨C, hC, hcoeff⟩
  refine ⟨⟨p, r, C, hr0', hC, hrp, ?_, hcoeff⟩⟩
  exact hR.mono (by exact_mod_cast hr0) hrR.le

/-- Quantitative local series data are equivalent to ordinary analyticity.
The forward implication is the useful extraction theorem; the reverse
implication records that no extra regularity assumption was introduced. -/
theorem analyticAt_iff_nonempty_localAnalyticMajorant
    {f : E → F} {x : E} :
    AnalyticAt ℝ f x ↔ Nonempty (LocalAnalyticMajorant f x) := by
  constructor
  · exact exists_localAnalyticMajorant_of_analyticAt
  · rintro ⟨M⟩
    exact M.analyticAt

end General

/-! ## CK normal-form specializations -/

/-- The seven-variable CK right-hand side has explicit local series data at
every phase point in `U_q`. -/
theorem exists_ckNormalForm_localAnalyticMajorant
    {P : Params} {v : CKPhase} (hU : CKPhaseInU P v) :
    Nonempty (LocalAnalyticMajorant (ckNormalForm P) v) :=
  exists_localAnalyticMajorant_of_analyticAt (analyticAt_ckNormalForm hU)

/-- The analytic factor left after extracting `y * Gamma₂` from the shifted
mixed-derivative coefficient has geometric local coefficient bounds. -/
theorem exists_shiftedCoeffXYFactor_localAnalyticMajorant
    {P : Params} {v : ShiftedPhase} (hU : ShiftedPhaseInU P v) :
    Nonempty (LocalAnalyticMajorant (shiftedCoeffXYFactor P) v) :=
  exists_localAnalyticMajorant_of_analyticAt (analyticAt_shiftedCoeffXYFactor hU)

/-- The analytic factor left after extracting `y²` from the shifted pure
tangential coefficient has geometric local coefficient bounds. -/
theorem exists_shiftedCoeffYYFactor_localAnalyticMajorant
    {P : Params} {v : ShiftedPhase} (hU : ShiftedPhaseInU P v) :
    Nonempty (LocalAnalyticMajorant (shiftedCoeffYYFactor P) v) :=
  exists_localAnalyticMajorant_of_analyticAt (analyticAt_shiftedCoeffYYFactor hU)

/-- The derivative-free shifted term has geometric local coefficient bounds. -/
theorem exists_shiftedConstant_localAnalyticMajorant
    {P : Params} {v : ShiftedPhase} (hU : ShiftedPhaseInU P v) :
    Nonempty (LocalAnalyticMajorant (shiftedConstant P) v) :=
  exists_localAnalyticMajorant_of_analyticAt (analyticAt_shiftedConstant hU)

/-- The shifted leading coefficient has geometric local coefficient bounds. -/
theorem exists_shiftedCoeff0_localAnalyticMajorant
    {P : Params} {v : ShiftedPhase} (hU : ShiftedPhaseInU P v) :
    Nonempty (LocalAnalyticMajorant
      (fun w : ShiftedPhase =>
        coeff0 (w 1) (shiftedLowJet w) (shiftedScalarData P w)) v) :=
  exists_localAnalyticMajorant_of_analyticAt (analyticAt_shiftedCoeff0 hU)

/-! The CK recursion is centered at the shifted origin, so it is useful to
record that all of the preceding packages are available there without an
additional neighborhood hypothesis. -/

/-- The shifted origin belongs to the shifted CK neighborhood. -/
theorem shiftedOrigin_inU (P : Params) :
    ShiftedPhaseInU P shiftedOrigin := by
  simpa only [ShiftedPhaseInU, shiftedOrigin, Pi.zero_apply,
    shiftedLowJet_origin] using
    (initialJet_inU P (y := 0) (by simpa using P.rho_pos))

/-- Local majorant data for the mixed-derivative analytic factor at the CK
base point. -/
theorem exists_shiftedCoeffXYFactor_origin_localAnalyticMajorant (P : Params) :
    Nonempty (LocalAnalyticMajorant
      (shiftedCoeffXYFactor P) shiftedOrigin) :=
  exists_shiftedCoeffXYFactor_localAnalyticMajorant (shiftedOrigin_inU P)

/-- Local majorant data for the pure-tangential analytic factor at the CK
base point. -/
theorem exists_shiftedCoeffYYFactor_origin_localAnalyticMajorant (P : Params) :
    Nonempty (LocalAnalyticMajorant
      (shiftedCoeffYYFactor P) shiftedOrigin) :=
  exists_shiftedCoeffYYFactor_localAnalyticMajorant (shiftedOrigin_inU P)

/-- Local majorant data for the derivative-free shifted term at the CK base
point. -/
theorem exists_shiftedConstant_origin_localAnalyticMajorant (P : Params) :
    Nonempty (LocalAnalyticMajorant
      (shiftedConstant P) shiftedOrigin) :=
  exists_shiftedConstant_localAnalyticMajorant (shiftedOrigin_inU P)

end

end StressTensor
