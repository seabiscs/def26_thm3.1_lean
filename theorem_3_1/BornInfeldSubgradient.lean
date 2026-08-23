import MaximalityOfU
import StressTensor.ActualFieldBridge
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

open Set

noncomputable section

namespace BornInfeldSubgradient

/-- The radial profile of the convex density `-J_q`. -/
def radialTildeDensity (q t : ℝ) : ℝ :=
  -Real.rpow (1 - Real.rpow t q) q⁻¹

private theorem outer_concave (q : ℝ) (hq1 : 1 < q) :
    ConcaveOn ℝ (Iic (1 : ℝ)) (fun s : ℝ => Real.rpow (1 - s) q⁻¹) := by
  have halpha0 : 0 ≤ q⁻¹ := inv_nonneg.mpr (le_of_lt (lt_trans zero_lt_one hq1))
  have halpha1 : q⁻¹ ≤ 1 := (inv_le_one₀ (lt_trans zero_lt_one hq1)).mpr hq1.le
  refine ⟨convex_Iic 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx0 : 0 ≤ 1 - x := sub_nonneg.mpr hx
  have hy0 : 0 ≤ 1 - y := sub_nonneg.mpr hy
  have h := (Real.concaveOn_rpow halpha0 halpha1).2 hx0 hy0 ha hb hab
  change
    a * Real.rpow (1 - x) q⁻¹ + b * Real.rpow (1 - y) q⁻¹ ≤
      Real.rpow (a * (1 - x) + b * (1 - y)) q⁻¹ at h
  change
    a * Real.rpow (1 - x) q⁻¹ + b * Real.rpow (1 - y) q⁻¹ ≤
      Real.rpow (1 - (a * x + b * y)) q⁻¹
  rw [show 1 - (a * x + b * y) = a * (1 - x) + b * (1 - y) by nlinarith]
  exact h

private theorem outer_convex (q : ℝ) (hq1 : 1 < q) :
    ConvexOn ℝ (Iic (1 : ℝ)) (fun s : ℝ => -Real.rpow (1 - s) q⁻¹) := by
  have hconc := outer_concave q hq1
  refine ⟨convex_Iic 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hconc.2 hx hy ha hb hab
  change
    a * Real.rpow (1 - x) q⁻¹ + b * Real.rpow (1 - y) q⁻¹ ≤
      Real.rpow (1 - (a * x + b * y)) q⁻¹ at h
  change
    -Real.rpow (1 - (a * x + b * y)) q⁻¹ ≤
      a • (-Real.rpow (1 - x) q⁻¹) + b • (-Real.rpow (1 - y) q⁻¹)
  simp only [smul_eq_mul]
  linarith

private theorem outer_monotone (q : ℝ) (hq1 : 1 < q) :
    MonotoneOn (fun s : ℝ => -Real.rpow (1 - s) q⁻¹) (Iic (1 : ℝ)) := by
  intro x hx y hy hxy
  have hy0 : 0 ≤ 1 - y := sub_nonneg.mpr hy
  have hbase : 1 - y ≤ 1 - x := by linarith
  have halpha0 : 0 ≤ q⁻¹ := inv_nonneg.mpr (le_of_lt (lt_trans zero_lt_one hq1))
  exact neg_le_neg (Real.rpow_le_rpow hy0 hbase halpha0)

theorem radialTildeDensity_convexOn_Icc
    {q : ℝ} (hq1 : 1 < q) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (radialTildeDensity q) := by
  let outer : ℝ → ℝ := fun s => -Real.rpow (1 - s) q⁻¹
  have hpow := convexOn_rpow hq1.le
  have hout := outer_convex q hq1
  have hmono := outer_monotone q hq1
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxpow : Real.rpow x q ≤ 1 := by
    simpa using Real.rpow_le_rpow hx.1 hx.2 (le_of_lt (lt_trans zero_lt_one hq1))
  have hypow : Real.rpow y q ≤ 1 := by
    simpa using Real.rpow_le_rpow hy.1 hy.2 (le_of_lt (lt_trans zero_lt_one hq1))
  have hcombo : a * x + b * y ∈ Icc (0 : ℝ) 1 :=
    (convex_Icc (0 : ℝ) 1) hx hy ha hb hab
  have hcomboPow : Real.rpow (a * x + b * y) q ≤ 1 := by
    simpa using Real.rpow_le_rpow hcombo.1 hcombo.2
      (le_of_lt (lt_trans zero_lt_one hq1))
  have hweightedPow : a * Real.rpow x q + b * Real.rpow y q ≤ 1 := by
    nlinarith
  have hpowerConvex :
      Real.rpow (a * x + b * y) q ≤
        a * Real.rpow x q + b * Real.rpow y q := by
    have h := hpow.2 hx.1 hy.1 ha hb hab
    change
      Real.rpow (a * x + b * y) q ≤
        a * Real.rpow x q + b * Real.rpow y q at h
    exact h
  have hfirst := hmono hcomboPow hweightedPow hpowerConvex
  have hsecond := hout.2 hxpow hypow ha hb hab
  simpa only [radialTildeDensity, outer, smul_eq_mul] using hfirst.trans hsecond

/-- The derivative of the radial profile at an interior positive radius. -/
theorem hasDerivAt_radialTildeDensity
    {q r : ℝ} (hq1 : 1 < q) (hr0 : 0 < r) (hr1 : r < 1) :
    HasDerivAt (-(fun t : ℝ => Real.rpow (1 - Real.rpow t q) q⁻¹))
      (Real.rpow r (q - 1) /
        Real.rpow (1 - Real.rpow r q) (1 - q⁻¹)) r := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq1)
  have hrpow_lt : Real.rpow r q < 1 := by
    simpa using Real.rpow_lt_rpow hr0.le hr1 (lt_trans zero_lt_one hq1)
  have hbase : 0 < 1 - Real.rpow r q := sub_pos.mpr hrpow_lt
  have hpow : HasDerivAt (fun t : ℝ => Real.rpow t q)
      (q * Real.rpow r (q - 1)) r := by
    simpa using Real.hasDerivAt_rpow_const (p := q) (Or.inl hr0.ne')
  have hinner : HasDerivAt (fun t : ℝ => 1 - Real.rpow t q)
      (-(q * Real.rpow r (q - 1))) r := by
    exact hpow.const_sub 1
  have hroot : HasDerivAt
      (fun t : ℝ => Real.rpow (1 - Real.rpow t q) q⁻¹)
      ((-(q * Real.rpow r (q - 1))) * q⁻¹ *
        Real.rpow (1 - Real.rpow r q) (q⁻¹ - 1)) r := by
    exact hinner.rpow_const (Or.inl hbase.ne')
  have hneg := hroot.neg
  have hcoeff :
      -(-(q * Real.rpow r (q - 1)) * q⁻¹ *
          Real.rpow (1 - Real.rpow r q) (q⁻¹ - 1)) =
        Real.rpow r (q - 1) /
          Real.rpow (1 - Real.rpow r q) (1 - q⁻¹) := by
    rw [show q⁻¹ - 1 = -(1 - q⁻¹) by ring]
    have hpowneg := Real.rpow_neg hbase.le (1 - q⁻¹)
    change Real.rpow (1 - Real.rpow r q) (-(1 - q⁻¹)) =
      (Real.rpow (1 - Real.rpow r q) (1 - q⁻¹))⁻¹ at hpowneg
    rw [hpowneg]
    field_simp [hq0]
  rw [hcoeff] at hneg
  exact hneg

/-- Supporting-line inequality for the radial profile. -/
theorem radial_supporting_line
    {q r s : ℝ} (hq1 : 1 < q) (hr0 : 0 < r) (hr1 : r < 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    radialTildeDensity q r +
        (Real.rpow r (q - 1) /
          Real.rpow (1 - Real.rpow r q) (1 - q⁻¹)) * (s - r) ≤
      radialTildeDensity q s := by
  let c := Real.rpow r (q - 1) /
    Real.rpow (1 - Real.rpow r q) (1 - q⁻¹)
  have hconv := radialTildeDensity_convexOn_Icc hq1
  have hrmem : r ∈ Icc (0 : ℝ) 1 := ⟨hr0.le, hr1.le⟩
  have hsmem : s ∈ Icc (0 : ℝ) 1 := ⟨hs0, hs1⟩
  have hderiv := hasDerivAt_radialTildeDensity hq1 hr0 hr1
  change HasDerivAt (-(fun t : ℝ => Real.rpow (1 - Real.rpow t q) q⁻¹)) c r at hderiv
  rcases lt_trichotomy r s with hrs | hrs | hsr
  · have hslope := hconv.le_slope_of_hasDerivAt hrmem hsmem hrs hderiv
    rw [slope_def_field] at hslope
    have hmul := (le_div_iff₀ (sub_pos.mpr hrs)).mp hslope
    dsimp only [c] at hmul ⊢
    linarith
  · subst s
    simp
  · have hslope := hconv.slope_le_of_hasDerivAt hsmem hrmem hsr hderiv
    rw [slope_def_field] at hslope
    have hmul := (div_le_iff₀ (sub_pos.mpr hsr)).mp hslope
    dsimp only [c] at hmul ⊢
    linarith

/-- The radial profile takes its minimum at radius zero. -/
theorem radial_zero_le
    {q s : ℝ} (hq1 : 1 < q) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    radialTildeDensity q 0 ≤ radialTildeDensity q s := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq1)
  have hqpos : 0 ≤ q := (lt_trans zero_lt_one hq1).le
  have hspow_nonneg : 0 ≤ Real.rpow s q := Real.rpow_nonneg hs0 q
  have hspow_le : Real.rpow s q ≤ 1 := by
    simpa using Real.rpow_le_rpow hs0 hs1 hqpos
  have hbase0 : 0 ≤ 1 - Real.rpow s q := sub_nonneg.mpr hspow_le
  have hbase1 : 1 - Real.rpow s q ≤ 1 := by linarith
  have halpha0 : 0 ≤ q⁻¹ := inv_nonneg.mpr hqpos
  have hroot := Real.rpow_le_rpow hbase0 hbase1 halpha0
  rw [Real.one_rpow] at hroot
  have hroot' :
      Real.rpow (1 - Real.rpow s q) q⁻¹ ≤ 1 := by
    simpa only [← Real.rpow_eq_pow] using hroot
  have hzero : Real.rpow 0 q = 0 := by
    rw [Real.rpow_eq_pow, Real.zero_rpow hq0]
  have hone : Real.rpow 1 q⁻¹ = 1 := by
    rw [Real.rpow_eq_pow, Real.one_rpow]
  rw [radialTildeDensity, hzero, sub_zero, hone]
  exact neg_le_neg hroot'

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The pointwise stress prescribed by the Born--Infeld integrand. -/
def canonicalStress (q : ℝ) (z : E) : E :=
  (Real.rpow ‖z‖ (q - 2) /
      Real.rpow (1 - Real.rpow ‖z‖ q) (1 - q⁻¹)) • z

omit [InnerProductSpace ℝ E] in
theorem tildeBornInfeldDensity_eq_radial
    {q : ℝ} {z : E} (hz : ‖z‖ ≤ 1) :
    MaximalityOfU.tildeBornInfeldDensity q z = radialTildeDensity q ‖z‖ := by
  rw [MaximalityOfU.tildeBornInfeldDensity,
    MaximalityOfU.bornInfeldDensity_of_norm_le hz]
  rfl

private theorem inner_canonicalStress_le_radial_term
    {q : ℝ} (hq1 : 1 < q) {z w : E} (hz0 : z ≠ 0) (hz1 : ‖z‖ < 1) :
    inner ℝ (canonicalStress q z) (w - z) ≤
      (Real.rpow ‖z‖ (q - 1) /
        Real.rpow (1 - Real.rpow ‖z‖ q) (1 - q⁻¹)) * (‖w‖ - ‖z‖) := by
  let r : ℝ := ‖z‖
  let d : ℝ := Real.rpow (1 - Real.rpow r q) (1 - q⁻¹)
  let A : ℝ := Real.rpow r (q - 2) / d
  have hr0 : 0 < r := by simpa only [r, norm_pos_iff] using hz0
  have hrpow_lt : Real.rpow r q < 1 := by
    simpa only [r, Real.rpow_eq_pow, Real.one_rpow] using
      Real.rpow_lt_rpow hr0.le hz1 (lt_trans zero_lt_one hq1)
  have hbase : 0 < 1 - Real.rpow r q := sub_pos.mpr hrpow_lt
  have hd0 : 0 ≤ d := Real.rpow_nonneg hbase.le (1 - q⁻¹)
  have hA0 : 0 ≤ A := by
    exact div_nonneg (Real.rpow_nonneg hr0.le (q - 2)) hd0
  have hinner : inner ℝ z w ≤ r * ‖w‖ := by
    simpa only [r] using real_inner_le_norm z w
  have hpowmul : Real.rpow r (q - 2) * r = Real.rpow r (q - 1) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add_one hr0.ne' (q - 2)]
    congr 1
    ring
  have hAr : A * r = Real.rpow r (q - 1) / d := by
    dsimp only [A]
    rw [div_mul_eq_mul_div, hpowmul]
  calc
    inner ℝ (canonicalStress q z) (w - z) =
        A * (inner ℝ z w - r ^ 2) := by
      simp only [canonicalStress, A, d, r, inner_smul_left,
        inner_sub_right, real_inner_self_eq_norm_sq, conj_trivial]
      ring
    _ ≤ A * (r * ‖w‖ - r ^ 2) := by
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right hinner _) hA0
    _ = (Real.rpow r (q - 1) / d) * (‖w‖ - r) := by
      rw [← hAr]
      ring
    _ = (Real.rpow ‖z‖ (q - 1) /
          Real.rpow (1 - Real.rpow ‖z‖ q) (1 - q⁻¹)) * (‖w‖ - ‖z‖) := by
      rfl

/-- The concrete Born--Infeld stress is a relative subgradient of `-J_q`. -/
theorem canonicalStress_isSubgradientAtOn
    {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2) {z : E} (hz : ‖z‖ < 1) :
    MaximalityOfU.IsSubgradientAtOn
      (MaximalityOfU.closedUnitBall : Set E)
      (MaximalityOfU.tildeBornInfeldDensity q) z (canonicalStress q z) := by
  refine ⟨hz.le, ?_⟩
  intro w hw
  change ‖w‖ ≤ 1 at hw
  rw [tildeBornInfeldDensity_eq_radial hz.le,
    tildeBornInfeldDensity_eq_radial hw]
  by_cases hz0 : z = 0
  · subst z
    have hqsub : q - 2 ≠ 0 := ne_of_lt (sub_neg.mpr hq2)
    have hstress : canonicalStress q (0 : E) = 0 := by
      simp [canonicalStress, Real.rpow_eq_pow, Real.zero_rpow hqsub]
    rw [hstress, inner_zero_left, add_zero]
    simpa only [norm_zero] using radial_zero_le hq1 (norm_nonneg w) hw
  · have hr0 : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hradial := radial_supporting_line hq1 hr0 hz (norm_nonneg w) hw
    have hinner := inner_canonicalStress_le_radial_term hq1 hz0 hz (w := w)
    calc
      radialTildeDensity q ‖z‖ + inner ℝ (canonicalStress q z) (w - z) ≤
          radialTildeDensity q ‖z‖ +
            (Real.rpow ‖z‖ (q - 1) /
              Real.rpow (1 - Real.rpow ‖z‖ q) (1 - q⁻¹)) *
                (‖w‖ - ‖z‖) := add_le_add_right hinner _
      _ ≤ radialTildeDensity q ‖w‖ := hradial

end Hilbert

/-! ## Bridge to the stress field from the analytic construction -/

/-- Convert the pair representation used by `StressTensor` to `Vector2`. -/
def pairToVector (v : ℝ × ℝ) : MaximalityOfU.Vector2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![v.1, v.2]

@[simp]
theorem pairToVector_apply (v : ℝ × ℝ) (i : Fin 2) :
    pairToVector v i = ![v.1, v.2] i := by
  simp [pairToVector]

theorem pairToVector_norm_sq (v : ℝ × ℝ) :
    ‖pairToVector v‖ ^ 2 = StressTensor.normSq v := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [pairToVector, StressTensor.normSq, Fin.sum_univ_two]

@[simp]
theorem pairToVector_smul (a : ℝ) (v : ℝ × ℝ) :
    pairToVector (a • v) = a • pairToVector v := by
  ext i
  fin_cases i <;> simp [pairToVector]

theorem normSq_rpow_half (v : ℝ × ℝ) (a : ℝ) :
    Real.rpow (StressTensor.normSq v) (a / 2) =
      Real.rpow ‖pairToVector v‖ a := by
  rw [← pairToVector_norm_sq]
  calc
    Real.rpow (‖pairToVector v‖ ^ 2) (a / 2) =
        Real.rpow |‖pairToVector v‖| (2 * (a / 2)) :=
      StressTensor.rpow_sq ‖pairToVector v‖ (a / 2)
    _ = Real.rpow ‖pairToVector v‖ a := by
      rw [abs_of_nonneg (norm_nonneg _)]
      congr 1
      ring

/-- The stress formula from `ActualFieldBridge`, after changing its pair
representation to `Vector2`, is exactly `canonicalStress`. -/
theorem pairToVector_energyGradientStress_eq_canonicalStress
    (P : StressTensor.Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) :
    pairToVector (StressTensor.energyGradientStress P γ x y) =
      canonicalStress P.q
        (pairToVector (StressTensor.actualAnsatzGradient γ x y)) := by
  let v := StressTensor.actualAnsatzGradient γ x y
  have hnum := normSq_rpow_half v (P.q - 2)
  have hdeficit := normSq_rpow_half v P.q
  rw [StressTensor.energyGradientStress, pairToVector_smul,
    StressTensor.energyGradientStressScalar, canonicalStress]
  change
    (Real.rpow (StressTensor.normSq v) ((P.q - 2) / 2) /
        Real.rpow (1 - Real.rpow (StressTensor.normSq v) (P.q / 2))
          (1 - 1 / P.q)) • pairToVector v =
      (Real.rpow ‖pairToVector v‖ (P.q - 2) /
        Real.rpow (1 - Real.rpow ‖pairToVector v‖ P.q)
          (1 - P.q⁻¹)) • pairToVector v
  rw [hnum, hdeficit]
  congr 2
  rw [one_div]

/-- Concrete relative-subgradient theorem for the stress field constructed in
`StressTensor.ActualFieldBridge`.  The exponent assumptions are bundled in
`P`; the only pointwise hypothesis is strict subluminality. -/
theorem energyGradientStress_isSubgradientAtOn
    (P : StressTensor.Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ)
    (hsub : StressTensor.normSq (StressTensor.actualAnsatzGradient γ x y) < 1) :
    MaximalityOfU.IsSubgradientAtOn
      (MaximalityOfU.closedUnitBall : Set MaximalityOfU.Vector2)
      (MaximalityOfU.tildeBornInfeldDensity P.q)
      (pairToVector (StressTensor.actualAnsatzGradient γ x y))
      (pairToVector (StressTensor.energyGradientStress P γ x y)) := by
  have hsq :
      ‖pairToVector (StressTensor.actualAnsatzGradient γ x y)‖ ^ 2 < 1 := by
    rw [pairToVector_norm_sq]
    exact hsub
  have hnorm :
      ‖pairToVector (StressTensor.actualAnsatzGradient γ x y)‖ < 1 :=
    (sq_lt_one_iff₀ (norm_nonneg _)).mp hsq
  rw [pairToVector_energyGradientStress_eq_canonicalStress]
  exact canonicalStress_isSubgradientAtOn P.one_lt_q P.q_lt_two hnorm

end BornInfeldSubgradient
