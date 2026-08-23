import StressTensor
import MaximalityOfU
import GammaMaximalityBridge

open Filter MeasureTheory Set Topology

noncomputable section

namespace GammaMaximalityBridge

/-! ## Uniform bounds supplied by the completed localization -/

/-- A convenient uniform upper bound for the analytic scalar factor on `V_q`. -/
theorem Stilde_lt_three_of_inV
    {P : StressTensor.Params} {t d : ℝ}
    (h : StressTensor.InV P t d) : StressTensor.Stilde P t d < 3 := by
  have hinvp_pos : 0 < 1 / P.p := div_pos zero_lt_one P.p_pos
  have hinvp_le_half : 1 / P.p ≤ (1 : ℝ) / 2 := by
    apply (div_le_iff₀ P.p_pos).2
    linarith [P.two_lt_p]
  have hquarter_pos : 0 < (1 : ℝ) / 4 := by norm_num
  have hquarter_le_one : (1 : ℝ) / 4 ≤ 1 := by norm_num
  have hquarter_exp :
      ((1 : ℝ) / 4) ^ ((1 : ℝ) / 2) ≤
        ((1 : ℝ) / 4) ^ (1 / P.p) :=
    Real.rpow_le_rpow_of_exponent_ge hquarter_pos hquarter_le_one hinvp_le_half
  have hquarter_sqrt :
      ((1 : ℝ) / 4) ^ ((1 : ℝ) / 2) = (1 : ℝ) / 2 := by
    rw [← Real.sqrt_eq_rpow]
    norm_num
  have hCpow :
      (1 : ℝ) / 2 <
        (StressTensor.Ctilde P t d) ^ (1 / P.p) := by
    calc
      (1 : ℝ) / 2 = ((1 : ℝ) / 4) ^ ((1 : ℝ) / 2) :=
        hquarter_sqrt.symm
      _ ≤ ((1 : ℝ) / 4) ^ (1 / P.p) := hquarter_exp
      _ < (StressTensor.Ctilde P t d) ^ (1 / P.p) :=
        Real.rpow_lt_rpow (by norm_num) h.Ctilde_bounds.1 hinvp_pos
  have hnum :
      (1 + t ^ 2 * d) ^ ((P.q - 2) / 2) < (4 : ℝ) / 3 := by
    simpa using h.segment_base_rpow_lt_four_thirds
      (show (1 : ℝ) ∈ Set.Icc 0 1 by simp)
  have hdenom_pos :
      0 < (StressTensor.Ctilde P t d) ^ (1 / P.p) :=
    Real.rpow_pos_of_pos h.Ctilde_pos _
  rw [StressTensor.Stilde]
  apply (div_lt_iff₀ hdenom_pos).2
  calc
    (1 + t ^ 2 * d) ^ ((P.q - 2) / 2) < (4 : ℝ) / 3 := hnum
    _ < 3 * (StressTensor.Ctilde P t d) ^ (1 / P.p) := by
      nlinarith [hCpow]

/-- The first ansatz factor is uniformly bounded on `U_q`. -/
theorem abs_gamma1_le_two_of_inU
    {P : StressTensor.Params} {x y : ℝ} {z : StressTensor.Jet}
    (hU : StressTensor.InU P x y z) :
    |StressTensor.gamma1 y z| ≤ 2 := by
  have hrho_sq_lt : P.rho ^ 2 < P.rho := by
    nlinarith [P.rho_pos, P.rho_lt_one]
  have hsmall : P.rho ^ 2 * (1 + P.rho) < 1 := by
    have hsum : 1 + P.rho < 2 := by linarith [P.rho_lt_one]
    have hprod : P.rho ^ 2 * (1 + P.rho) < P.rho * 2 :=
      mul_lt_mul'' hrho_sq_lt hsum (sq_nonneg _) (by linarith [P.rho_pos])
    linarith [P.rho_lt_one_div_1024]
  have hperturb : |StressTensor.gamma1 y z - 1| < 1 :=
    lt_trans (StressTensor.abs_gamma1_sub_one_lt hU) hsmall
  have hupper : StressTensor.gamma1 y z < 2 := by
    linarith [(abs_lt.mp hperturb).2]
  have hpos : 0 < StressTensor.gamma1 y z := by
    linarith [StressTensor.gamma1_ge_one_half hU]
  rw [abs_of_pos hpos]
  exact hupper.le

/-- The second ansatz factor is uniformly bounded on `U_q`. -/
theorem abs_gamma2_le_one_of_inU
    {P : StressTensor.Params} {x y : ℝ} {z : StressTensor.Jet}
    (hU : StressTensor.InU P x y z) :
    |StressTensor.gamma2 y z| ≤ 1 := by
  have hsum : 1 + P.rho < 2 := by linarith [P.rho_lt_one]
  have hprod : P.rho * (1 + P.rho) < P.rho * 2 :=
    mul_lt_mul_of_pos_left hsum P.rho_pos
  exact (StressTensor.abs_gamma2_lt hU).le.trans <| by
    linarith [hprod, P.rho_lt_one_half]

/-- Both analytic factors occurring in (3.27) are bounded by the same
numerical constant throughout a localized square. -/
theorem localized_factor_bounds
    {P : StressTensor.Params} {gamma : ℝ → ℝ → ℝ}
    {U : Set StressTensor.Point}
    (L : StressTensor.CompactSquareLocalization P gamma U)
    {w : StressTensor.Point} (hw : w ∈ StressTensor.closedSquare L.ell) :
    |StressTensor.scalarField P gamma w.1 w.2 *
        StressTensor.gamma1Field gamma w.1 w.2| ≤ 6 ∧
      |StressTensor.scalarField P gamma w.1 w.2 *
        StressTensor.gamma2Field gamma w.1 w.2| ≤ 6 := by
  have hU := L.jet_inU w hw
  have hV := StressTensor.inV_gamma0_of_inU hU
  have hSlt : StressTensor.scalarField P gamma w.1 w.2 < 3 := by
    simpa [StressTensor.scalarField, StressTensor.scalarDataField,
      StressTensor.scalarDataOfJet, StressTensor.scalarDataAt,
      StressTensor.gamma0Field] using Stilde_lt_three_of_inV hV
  have hSnonneg : 0 ≤ StressTensor.scalarField P gamma w.1 w.2 := by
    have := StressTensor.one_eighth_le_Scomp_of_inU hU
    have hzero : (0 : ℝ) ≤ (1 : ℝ) / 8 := by norm_num
    simpa [StressTensor.Scomp, StressTensor.scalarField,
      StressTensor.scalarDataField, StressTensor.scalarDataOfJet,
      StressTensor.scalarDataAt, StressTensor.gamma0Field] using hzero.trans this
  have hgamma1 : |StressTensor.gamma1Field gamma w.1 w.2| ≤ 2 := by
    simpa [StressTensor.gamma1Field] using abs_gamma1_le_two_of_inU hU
  have hgamma2 : |StressTensor.gamma2Field gamma w.1 w.2| ≤ 1 := by
    simpa [StressTensor.gamma2Field] using abs_gamma2_le_one_of_inU hU
  rw [abs_mul, abs_of_nonneg hSnonneg, abs_mul, abs_of_nonneg hSnonneg]
  constructor
  · nlinarith [abs_nonneg (StressTensor.gamma1Field gamma w.1 w.2)]
  · nlinarith [abs_nonneg (StressTensor.gamma2Field gamma w.1 w.2)]

/-! ## Measurability of the actual localized stress -/

/-- Analyticity of `gamma` on the localization domain makes all three
factors in the singular-stress formula continuous on the closed square. -/
theorem localized_factor_fields_continuousOn
    {P : StressTensor.Params} {gamma : ℝ → ℝ → ℝ}
    {U : Set StressTensor.Point}
    (L : StressTensor.CompactSquareLocalization P gamma U)
    (hanalytic : AnalyticOnNhd ℝ (StressTensor.uncurried gamma) U) :
    ContinuousOn
        (fun w : StressTensor.Point =>
          StressTensor.scalarField P gamma w.1 w.2) (StressTensor.closedSquare L.ell) ∧
      ContinuousOn
        (fun w : StressTensor.Point =>
          StressTensor.gamma1Field gamma w.1 w.2) (StressTensor.closedSquare L.ell) ∧
      ContinuousOn
        (fun w : StressTensor.Point =>
          StressTensor.gamma2Field gamma w.1 w.2) (StressTensor.closedSquare L.ell) := by
  have hfields : ∀ w ∈ StressTensor.closedSquare L.ell,
      ContinuousAt
          (fun v : StressTensor.Point =>
            StressTensor.scalarField P gamma v.1 v.2) w ∧
        ContinuousAt
          (fun v : StressTensor.Point =>
            StressTensor.gamma1Field gamma v.1 v.2) w ∧
        ContinuousAt
          (fun v : StressTensor.Point =>
            StressTensor.gamma2Field gamma v.1 v.2) w := by
    intro w hw
    have hgamma : AnalyticAt ℝ (StressTensor.uncurried gamma) w :=
      hanalytic w (L.closed_subset_domain hw)
    have hjet := StressTensor.derivativeJetContinuousAt_of_analyticAt hgamma
    have hval : ContinuousAt
        (fun v : StressTensor.Point => (StressTensor.jetOf gamma v.1 v.2).val) w := by
      change ContinuousAt (StressTensor.uncurried gamma) w
      exact hgamma.continuousAt
    have hgamma1 : ContinuousAt
        (fun v : StressTensor.Point =>
          StressTensor.gamma1Field gamma v.1 v.2) w := by
      change ContinuousAt (fun v : StressTensor.Point =>
        1 + v.2 ^ 2 * (StressTensor.jetOf gamma v.1 v.2).dx) w
      convert continuousAt_const.add
        ((continuousAt_snd.pow 2).mul hjet.dx) using 1
      all_goals rfl
    have hgamma2 : ContinuousAt
        (fun v : StressTensor.Point =>
          StressTensor.gamma2Field gamma v.1 v.2) w := by
      change ContinuousAt (fun v : StressTensor.Point =>
        (StressTensor.jetOf gamma v.1 v.2).val +
          v.2 * (StressTensor.jetOf gamma v.1 v.2).dy / 2) w
      convert hval.add ((continuousAt_snd.mul hjet.dy).div_const 2) using 1
      all_goals rfl
    have hgamma0 : ContinuousAt
        (fun v : StressTensor.Point =>
          StressTensor.gamma0Field gamma v.1 v.2) w := by
      change ContinuousAt (fun v : StressTensor.Point =>
        2 * (StressTensor.jetOf gamma v.1 v.2).dx +
          v.2 ^ 2 * (StressTensor.jetOf gamma v.1 v.2).dx ^ 2 +
          4 * StressTensor.gamma2Field gamma v.1 v.2 ^ 2) w
      convert ((hjet.dx.const_mul 2).add
        ((continuousAt_snd.pow 2).mul (hjet.dx.pow 2))).add
          ((hgamma2.pow 2).const_mul 4) using 1
      all_goals rfl
    have hscalarPoint : ContinuousAt
        (fun v : StressTensor.Point =>
          (v.2, StressTensor.gamma0Field gamma v.1 v.2)) w :=
      continuousAt_snd.prodMk hgamma0
    have hscalarBase : ContinuousAt (StressTensor.stildeUncurried P)
        (w.2, StressTensor.gamma0Field gamma w.1 w.2) :=
      (StressTensor.analyticAt_stildeUncurried_of_mem
        (StressTensor.scalarPoint_mem_scalarAnalyticRegion_of_inU
          (L.jet_inU w hw))).continuousAt
    have hscalar : ContinuousAt
        (fun v : StressTensor.Point =>
          StressTensor.scalarField P gamma v.1 v.2) w := by
      change ContinuousAt
        (StressTensor.stildeUncurried P ∘
          fun v : StressTensor.Point =>
            (v.2, StressTensor.gamma0Field gamma v.1 v.2)) w
      exact hscalarBase.comp
        (f := fun v : StressTensor.Point =>
          (v.2, StressTensor.gamma0Field gamma v.1 v.2)) hscalarPoint
    exact ⟨hscalar, hgamma1, hgamma2⟩
  exact ⟨fun w hw => (hfields w hw).1.continuousWithinAt,
    fun w hw => (hfields w hw).2.1.continuousWithinAt,
    fun w hw => (hfields w hw).2.2.continuousWithinAt⟩

/-- The zero-on-axis representative of the singular stress is strongly
measurable almost everywhere on the localized cube.  This supplies the
measurability part implicit in the manuscript notation
`L^{p/2,∞}(Q_p,ℝ²)`. -/
theorem localized_stressField_aestronglyMeasurable
    {P : StressTensor.Params} {gamma : ℝ → ℝ → ℝ}
    {U : Set StressTensor.Point}
    (L : StressTensor.CompactSquareLocalization P gamma U)
    (hanalytic : AnalyticOnNhd ℝ (StressTensor.uncurried gamma) U) :
    AEStronglyMeasurable (stressField P gamma)
      (volume.restrict (MaximalityOfU.cube L.ell)) := by
  let mu := volume.restrict (MaximalityOfU.cube L.ell)
  have hcubeClosed : MaximalityOfU.cube L.ell ⊆
      StressTensor.closedSquare L.ell := by
    intro z hz
    exact ⟨abs_le.mpr ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
      abs_le.mpr ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  have hcontinuous := localized_factor_fields_continuousOn L hanalytic
  have hS : AEStronglyMeasurable
      (fun w : StressTensor.Point =>
        StressTensor.scalarField P gamma w.1 w.2) mu := by
    exact hcontinuous.1.aestronglyMeasurable_of_subset_isCompact
      (StressTensor.isCompact_closedSquare L.ell)
      (MaximalityOfU.cube_measurable L.ell) hcubeClosed
  have hG1 : AEStronglyMeasurable
      (fun w : StressTensor.Point =>
        StressTensor.gamma1Field gamma w.1 w.2) mu := by
    exact hcontinuous.2.1.aestronglyMeasurable_of_subset_isCompact
      (StressTensor.isCompact_closedSquare L.ell)
      (MaximalityOfU.cube_measurable L.ell) hcubeClosed
  have hG2 : AEStronglyMeasurable
      (fun w : StressTensor.Point =>
        StressTensor.gamma2Field gamma w.1 w.2) mu := by
    exact hcontinuous.2.2.aestronglyMeasurable_of_subset_isCompact
      (StressTensor.isCompact_closedSquare L.ell)
      (MaximalityOfU.cube_measurable L.ell) hcubeClosed
  have hy : AEStronglyMeasurable
      (fun w : StressTensor.Point => w.2) mu :=
    continuous_snd.aestronglyMeasurable
  have hpowReal : Measurable
      (fun y : ℝ => |y| ^ (-(2 / P.p))) := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro y hy0
    exact (continuous_abs.continuousAt.rpow_const
      (Or.inl (abs_ne_zero.mpr hy0))).continuousWithinAt
  have hpow : AEStronglyMeasurable
      (fun w : StressTensor.Point => |w.2| ^ (-(2 / P.p))) mu :=
    (hpowReal.comp measurable_snd).aestronglyMeasurable
  have hcoord0 : AEStronglyMeasurable
      (fun w : StressTensor.Point =>
        |w.2| ^ (-(2 / P.p)) *
          StressTensor.scalarField P gamma w.1 w.2 *
          StressTensor.gamma1Field gamma w.1 w.2) mu := by
    convert (hpow.mul hS).mul hG1 using 1
    all_goals rfl
  have hcoord1 : AEStronglyMeasurable
      (fun w : StressTensor.Point =>
        2 * w.2 * |w.2| ^ (-(2 / P.p)) *
          StressTensor.scalarField P gamma w.1 w.2 *
          StressTensor.gamma2Field gamma w.1 w.2) mu := by
    convert (((hy.const_mul 2).mul hpow).mul hS).mul hG2 using 1
    all_goals rfl
  have htoVector : Continuous (fun ab : ℝ × ℝ =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![ab.1, ab.2]) := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    fun_prop
  have hvector : AEStronglyMeasurable
      (fun w : StressTensor.Point =>
        (EuclideanSpace.equiv (Fin 2) ℝ).symm
          ![|w.2| ^ (-(2 / P.p)) *
              StressTensor.scalarField P gamma w.1 w.2 *
              StressTensor.gamma1Field gamma w.1 w.2,
            2 * w.2 * |w.2| ^ (-(2 / P.p)) *
              StressTensor.scalarField P gamma w.1 w.2 *
              StressTensor.gamma2Field gamma w.1 w.2]) mu := by
    exact htoVector.comp_aestronglyMeasurable (hcoord0.prodMk hcoord1)
  have hoff : MeasurableSet {w : StressTensor.Point | w.2 ≠ 0} := by
    exact (measurable_snd (measurableSet_singleton 0)).compl
  have hindicator := hvector.indicator hoff
  change AEStronglyMeasurable (stressField P gamma) mu
  apply hindicator.congr
  filter_upwards [] with w
  have hexponent : -(2 / P.p) = -2 / P.p := by ring
  by_cases hy0 : w.2 = 0
  · simp [stressField, MaximalityOfU.stressRepresentative,
      Set.indicator, hy0]
  · simp [stressField, MaximalityOfU.stressRepresentative,
      Set.indicator, hy0, hexponent]

/-- The Euclidean norm of a two-vector is bounded by the sum of the absolute
values of its two coordinates. -/
theorem vector2_norm_le_abs_coords (v : MaximalityOfU.Vector2) :
    ‖v‖ ≤
      |(EuclideanSpace.equiv (Fin 2) ℝ) v 0| +
        |(EuclideanSpace.equiv (Fin 2) ℝ) v 1| := by
  apply (sq_le_sq₀ (norm_nonneg v)
    (add_nonneg (abs_nonneg _) (abs_nonneg _))).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two]
  change
    ((EuclideanSpace.equiv (Fin 2) ℝ) v 0) ^ 2 +
        ((EuclideanSpace.equiv (Fin 2) ℝ) v 1) ^ 2 ≤
      (|(EuclideanSpace.equiv (Fin 2) ℝ) v 0| +
        |(EuclideanSpace.equiv (Fin 2) ℝ) v 1|) ^ 2
  calc
    ((EuclideanSpace.equiv (Fin 2) ℝ) v 0) ^ 2 +
        ((EuclideanSpace.equiv (Fin 2) ℝ) v 1) ^ 2 =
      |(EuclideanSpace.equiv (Fin 2) ℝ) v 0| ^ 2 +
        |(EuclideanSpace.equiv (Fin 2) ℝ) v 1| ^ 2 := by
          rw [sq_abs, sq_abs]
    _ ≤ |(EuclideanSpace.equiv (Fin 2) ℝ) v 0| ^ 2 +
          |(EuclideanSpace.equiv (Fin 2) ℝ) v 1| ^ 2 +
          2 * |(EuclideanSpace.equiv (Fin 2) ℝ) v 0| *
            |(EuclideanSpace.equiv (Fin 2) ℝ) v 1| := by
      have hcross : 0 ≤
          2 * |(EuclideanSpace.equiv (Fin 2) ℝ) v 0| *
            |(EuclideanSpace.equiv (Fin 2) ℝ) v 1| := by positivity
      linarith
    _ = (|(EuclideanSpace.equiv (Fin 2) ℝ) v 0| +
        |(EuclideanSpace.equiv (Fin 2) ℝ) v 1|) ^ 2 := by ring

/-- A completed compact localization supplies the full vector estimate in
(3.27), without any additional Taylor-remainder or factor-bound hypothesis. -/
theorem localized_stressField_power_bound
    {P : StressTensor.Params} {gamma : ℝ → ℝ → ℝ}
    {U : Set StressTensor.Point}
    (L : StressTensor.CompactSquareLocalization P gamma U) :
    ∀ z, z ∈ MaximalityOfU.cube L.ell → z.2 ≠ 0 →
      ‖stressField P gamma z‖ ≤
        18 * |z.2| ^ (-MaximalityOfU.singularityExponent P.p) := by
  intro z hz hy0
  have hzClosed : z ∈ StressTensor.closedSquare L.ell := by
    rcases z with ⟨x, y⟩
    rcases hz with ⟨hx, hy⟩
    exact ⟨abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩,
      abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩⟩
  have hU := L.jet_inU z hzClosed
  have hfactors := localized_factor_bounds L hzClosed
  have hcoord0 := abs_stressField_coord_zero_le
    P gamma hy0 hfactors.1
  have hcoord1decay := abs_normalStress_le P gamma hy0 hfactors.2
  have hyabs_pos : 0 < |z.2| := abs_pos.mpr hy0
  have hyabs_le_one : |z.2| ≤ 1 := by
    exact (lt_trans hU.abs_y_lt P.rho_lt_one).le
  have hexponents :
      -MaximalityOfU.singularityExponent P.p ≤
        MaximalityOfU.decayExponent P.p := by
    simp only [MaximalityOfU.singularityExponent,
      MaximalityOfU.decayExponent]
    linarith
  have hpower :
      |z.2| ^ MaximalityOfU.decayExponent P.p ≤
        |z.2| ^ (-MaximalityOfU.singularityExponent P.p) :=
    Real.rpow_le_rpow_of_exponent_ge hyabs_pos hyabs_le_one hexponents
  have hcoord1 :
      |(EuclideanSpace.equiv (Fin 2) ℝ) (stressField P gamma z) 1| ≤
        12 * |z.2| ^ (-MaximalityOfU.singularityExponent P.p) := by
    change |normalStress P gamma z.1 z.2| ≤ _
    calc
      |normalStress P gamma z.1 z.2| ≤
          2 * 6 * |z.2| ^ MaximalityOfU.decayExponent P.p := hcoord1decay
      _ ≤ 12 * |z.2| ^ (-MaximalityOfU.singularityExponent P.p) := by
        nlinarith [Real.rpow_nonneg (abs_nonneg z.2)
          (MaximalityOfU.decayExponent P.p),
          Real.rpow_nonneg (abs_nonneg z.2)
            (-MaximalityOfU.singularityExponent P.p)]
  calc
    ‖stressField P gamma z‖ ≤
        |(EuclideanSpace.equiv (Fin 2) ℝ) (stressField P gamma z) 0| +
          |(EuclideanSpace.equiv (Fin 2) ℝ) (stressField P gamma z) 1| :=
      vector2_norm_le_abs_coords _
    _ ≤ 6 * |z.2| ^ (-MaximalityOfU.singularityExponent P.p) +
          12 * |z.2| ^ (-MaximalityOfU.singularityExponent P.p) :=
      add_le_add hcoord0 hcoord1
    _ = 18 * |z.2| ^ (-MaximalityOfU.singularityExponent P.p) := by ring

/-- The localized singular stress is Bochner integrable.  The pointwise
power bound is integrable because `2 / p < 1`; the light axis itself causes
no issue because the chosen representative vanishes there. -/
theorem localized_stressField_integrableOn_cube
    {P : StressTensor.Params} {gamma : ℝ → ℝ → ℝ}
    {U : Set StressTensor.Point}
    (L : StressTensor.CompactSquareLocalization P gamma U)
    (hanalytic : AnalyticOnNhd ℝ (StressTensor.uncurried gamma) U) :
    IntegrableOn (stressField P gamma) (MaximalityOfU.cube L.ell) volume := by
  apply stressField_integrableOn_cube_of_power_bound
    (c := 18) P gamma L.ell_pos
      (localized_stressField_aestronglyMeasurable L hanalytic)
  filter_upwards [ae_restrict_mem (MaximalityOfU.cube_measurable L.ell)] with z hz
  by_cases hy0 : z.2 = 0
  · rcases z with ⟨x, y⟩
    simp_all [stressField]
    positivity
  · exact localized_stressField_power_bound L z hz hy0

/-- Hence the actual localized stress has the finite-domain distribution
tail with exponent `p/2`. -/
theorem localized_stressField_has_weak_p_over_two_tail
    {P : StressTensor.Params} {gamma : ℝ → ℝ → ℝ}
    {U : Set StressTensor.Point}
    (L : StressTensor.CompactSquareLocalization P gamma U) :
    MaximalityOfU.HasWeakLpTailOn volume
      (MaximalityOfU.weakExponent P.p)
      (MaximalityOfU.cube L.ell) (stressField P gamma) := by
  exact stressField_has_weak_p_over_two_tail_of_power_bound
    P gamma L.ell_pos.le (by norm_num)
      (localized_stressField_power_bound L)

/-- The exponent `p/2` is exactly the manuscript exponent
`q / (2 * (q - 1))`. -/
theorem Params.weakExponent_eq_paperExponent (P : StressTensor.Params) :
    MaximalityOfU.weakExponent P.p = P.q / (2 * (P.q - 1)) := by
  rw [Params.p_eq_conjugateExponent P]
  exact MaximalityOfU.weakExponent_conjugate P.one_lt_q

/-- Paper-facing spelling of the same weak-tail conclusion. -/
theorem localized_stressField_has_weak_paper_tail
    {P : StressTensor.Params} {gamma : ℝ → ℝ → ℝ}
    {U : Set StressTensor.Point}
    (L : StressTensor.CompactSquareLocalization P gamma U) :
    MaximalityOfU.HasWeakLpTailOn volume
      (P.q / (2 * (P.q - 1)))
      (MaximalityOfU.cube L.ell) (stressField P gamma) := by
  rw [← Params.weakExponent_eq_paperExponent P]
  exact localized_stressField_has_weak_p_over_two_tail L

/-- A paper-facing package of the two logical ingredients of weak
`L^{q/[2(q-1)]}` membership: local strong measurability and the uniform
distribution-function estimate. -/
theorem localized_stressField_measurable_and_has_weak_paper_tail
    {P : StressTensor.Params} {gamma : ℝ → ℝ → ℝ}
    {U : Set StressTensor.Point}
    (L : StressTensor.CompactSquareLocalization P gamma U)
    (hanalytic : AnalyticOnNhd ℝ (StressTensor.uncurried gamma) U) :
    AEStronglyMeasurable (stressField P gamma)
        (volume.restrict (MaximalityOfU.cube L.ell)) ∧
      MaximalityOfU.HasWeakLpTailOn volume
        (P.q / (2 * (P.q - 1)))
        (MaximalityOfU.cube L.ell) (stressField P gamma) :=
  ⟨localized_stressField_aestronglyMeasurable L hanalytic,
    localized_stressField_has_weak_paper_tail L⟩

end GammaMaximalityBridge
