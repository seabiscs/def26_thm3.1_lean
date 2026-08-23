import StressTensor.FirstOrderFieldBridge
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Reconstruction from the reduced first-order fields

Given reduced fields `(v,r)` with zero `x=0` data, define

`h(x,y) = ∫₀ˣ v(s,y) ds`, `gamma(x,y)=h(x,y)-x`.

The fundamental theorem of calculus gives `h_x=v`.  To keep differentiation
under the parameter integral completely explicit, `FirstOrderReconstructionData`
stores the witness

`h_y(x,y) = ∫₀ˣ v_y(s,y) ds`.

This witness follows from the standard dominated parametric-integral theorem;
it is exposed here rather than hidden behind an unproved regularity claim.
The second reduced equation then propagates the compatibility identity
`r=gamma+(y/2)gamma_y`.  Consequently the first reduced equation implies the
original auxiliary equation through `FirstOrderFieldBridge`.
-/

namespace StressTensor

noncomputable section

/-! ## Integral reconstruction -/

/-- The zero-initial-value antiderivative of `v` in the `x` variable. -/
def reconstructedH (v : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..x, v s y

/-- The candidate original unknown reconstructed from `v`. -/
def reconstructedGamma (v : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  reconstructedH v x y - x

/-- The expected `y` derivative of `reconstructedH`, written as the integral
of the actual `y` derivative of `v`. -/
def reconstructedHY (v : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..x, partialY v s y

@[simp] theorem reconstructedH_zero (v : ℝ → ℝ → ℝ) (y : ℝ) :
    reconstructedH v 0 y = 0 := by
  simp [reconstructedH]

@[simp] theorem reconstructedHY_zero (v : ℝ → ℝ → ℝ) (y : ℝ) :
    reconstructedHY v 0 y = 0 := by
  simp [reconstructedHY]

@[simp] theorem reconstructedGamma_zero
    (v : ℝ → ℝ → ℝ) (y : ℝ) :
    reconstructedGamma v 0 y = 0 := by
  simp [reconstructedGamma]

/-! ## Local analytic regularity on centered boxes -/

/-- The centered rectangle on which the reduced analytic field is realized. -/
def reconstructionBox (rx ry : ℝ) : Set Point :=
  Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry

@[simp] theorem mem_reconstructionBox {rx ry x y : ℝ} :
    (x, y) ∈ reconstructionBox rx ry ↔ |x| < rx ∧ |y| < ry := by
  simp [reconstructionBox, abs_lt]

/-- A segment from the Cauchy axis to an interior point of a centered
interval remains in that interval. -/
theorem abs_lt_of_mem_uIcc_zero {rx x s : ℝ}
    (hx : |x| < rx) (hs : s ∈ Set.uIcc (0 : ℝ) x) :
    |s| < rx := by
  rcases le_total (0 : ℝ) x with hx0 | hx0
  · rw [Set.uIcc_of_le hx0] at hs
    rw [abs_of_nonneg hx0] at hx
    rw [abs_of_nonneg hs.1]
    exact lt_of_le_of_lt hs.2 hx
  · rw [Set.uIcc_of_ge hx0] at hs
    rw [abs_of_nonpos hx0] at hx
    rw [abs_of_nonpos hs.2]
    exact lt_of_le_of_lt (neg_le_neg hs.1) hx

/-- The tangential derivative of a two-variable analytic function is
continuous at the same point.  This formulation is useful because
`partialY` is defined through the one-variable `deriv`, while analyticity is
stated for the uncurried function. -/
theorem continuousAt_uncurried_partialY_of_analyticAt
    {v : ℝ → ℝ → ℝ} {x y : ℝ}
    (hv : AnalyticAt ℝ (uncurried v) (x, y)) :
    ContinuousAt (fun z : Point => partialY v z.1 z.2) (x, y) := by
  let f : Point → ℝ := uncurried v
  let ey : Point := (0, 1)
  have hfd : AnalyticAt ℝ (fderiv ℝ f) (x, y) := by
    simpa only [f] using hv.fderiv
  have heval : AnalyticAt ℝ (fun z => fderiv ℝ f z ey) (x, y) :=
    (hfd.contDiffAt.clm_apply contDiffAt_const).analyticAt
  have hev : ∀ᶠ z in nhds (x, y), AnalyticAt ℝ f z := by
    simpa only [f] using hv.eventually_analyticAt
  have heq :
      (fun z : Point => partialY v z.1 z.2) =ᶠ[nhds (x, y)]
        (fun z => fderiv ℝ f z ey) := by
    filter_upwards [hev] with z hz
    simpa only [f, ey] using
      partialY_eq_fderiv_uncurried hz.differentiableAt
  exact heval.continuousAt.congr_of_eventuallyEq heq

/-- Hence `partialY v` is continuous throughout every set on which `v` is
analytic on neighborhoods. -/
theorem continuousOn_uncurried_partialY_of_analyticOnNhd
    {v : ℝ → ℝ → ℝ} {s : Set Point}
    (hv : AnalyticOnNhd ℝ (uncurried v) s) :
    ContinuousOn (fun z : Point => partialY v z.1 z.2) s := by
  intro z hz
  exact (continuousAt_uncurried_partialY_of_analyticAt (hv z hz)).continuousWithinAt

/-- Local FTC in the evolution variable.  Only analyticity on the centered
box is needed, because the integration segment from `0` to `x` remains in
the box. -/
theorem hasDerivAt_reconstructedH_x_of_analyticOnNhd
    {v : ℝ → ℝ → ℝ} {rx ry x y : ℝ}
    (hv : AnalyticOnNhd ℝ (uncurried v) (reconstructionBox rx ry))
    (hx : |x| < rx) (hy : |y| < ry) :
    HasDerivAt (fun xi => reconstructedH v xi y) (v x y) x := by
  have hpath : Continuous (fun s : ℝ => (s, y)) :=
    continuous_id.prodMk continuous_const
  have hcontOpen : ContinuousOn (fun s => v s y) (Set.Ioo (-rx) rx) := by
    simpa [uncurried] using hv.continuousOn.comp' hpath.continuousOn (by
      intro s hs
      exact mem_reconstructionBox.2 ⟨abs_lt.mpr hs, hy⟩)
  have hseg : Set.uIcc (0 : ℝ) x ⊆ Set.Ioo (-rx) rx := by
    intro s hs
    exact abs_lt.mp (abs_lt_of_mem_uIcc_zero hx hs)
  have hcontOn : ContinuousOn (fun s => v s y) (Set.uIcc (0 : ℝ) x) :=
    hcontOpen.mono hseg
  have hcontAt : ContinuousAt (fun s => v s y) x := by
    exact hcontOpen.continuousAt (isOpen_Ioo.mem_nhds (abs_lt.mp hx))
  simpa only [reconstructedH] using
    intervalIntegral.integral_hasDerivAt_right hcontOn.intervalIntegrable
      (hcontOpen.stronglyMeasurableAtFilter isOpen_Ioo x (abs_lt.mp hx)) hcontAt

/-- Local FTC for the integrated tangential derivative. -/
theorem hasDerivAt_reconstructedHY_x_of_analyticOnNhd
    {v : ℝ → ℝ → ℝ} {rx ry x y : ℝ}
    (hv : AnalyticOnNhd ℝ (uncurried v) (reconstructionBox rx ry))
    (hx : |x| < rx) (hy : |y| < ry) :
    HasDerivAt (fun xi => reconstructedHY v xi y) (partialY v x y) x := by
  have hpartial := continuousOn_uncurried_partialY_of_analyticOnNhd hv
  have hpath : Continuous (fun s : ℝ => (s, y)) :=
    continuous_id.prodMk continuous_const
  have hcontOpen : ContinuousOn (fun s => partialY v s y) (Set.Ioo (-rx) rx) := by
    simpa only [Function.comp_apply] using hpartial.comp' hpath.continuousOn (by
      intro s hs
      exact mem_reconstructionBox.2 ⟨abs_lt.mpr hs, hy⟩)
  have hseg : Set.uIcc (0 : ℝ) x ⊆ Set.Ioo (-rx) rx := by
    intro s hs
    exact abs_lt.mp (abs_lt_of_mem_uIcc_zero hx hs)
  have hcontOn : ContinuousOn (fun s => partialY v s y)
      (Set.uIcc (0 : ℝ) x) := hcontOpen.mono hseg
  have hcontAt : ContinuousAt (fun s => partialY v s y) x := by
    exact hcontOpen.continuousAt (isOpen_Ioo.mem_nhds (abs_lt.mp hx))
  simpa only [reconstructedHY] using
    intervalIntegral.integral_hasDerivAt_right hcontOn.intervalIntegrable
      (hcontOpen.stronglyMeasurableAtFilter isOpen_Ioo x (abs_lt.mp hx)) hcontAt

/-- Differentiation under the reconstruction integral.  The proof uses
Mathlib's dominated parametric interval-integral theorem on the compact
rectangle `uIcc 0 x × Icc ((y-r_y)/2) ((y+r_y)/2)`.  Analyticity supplies the
derivative and continuity, compactness supplies a uniform bound, and centered
convexity keeps the entire rectangle inside the analytic box. -/
theorem hasDerivAt_reconstructedH_y_of_analyticOnNhd
    {v : ℝ → ℝ → ℝ} {rx ry x y : ℝ}
    (hv : AnalyticOnNhd ℝ (uncurried v) (reconstructionBox rx ry))
    (hx : |x| < rx) (hy : |y| < ry) :
    HasDerivAt (fun eta => reconstructedH v x eta)
      (reconstructedHY v x y) y := by
  let yl : ℝ := (y - ry) / 2
  let yu : ℝ := (y + ry) / 2
  let K : Set Point := Set.uIcc (0 : ℝ) x ×ˢ Set.Icc yl yu
  have hyBounds : -ry < y ∧ y < ry := (abs_lt.mp hy)
  have hyl : yl < y := by
    dsimp only [yl]
    linarith
  have hyu : y < yu := by
    dsimp only [yu]
    linarith
  have hKsub : K ⊆ reconstructionBox rx ry := by
    rintro ⟨s, eta⟩ ⟨hs, heta⟩
    apply mem_reconstructionBox.2
    refine ⟨abs_lt_of_mem_uIcc_zero hx hs, ?_⟩
    rw [abs_lt]
    dsimp only [yl, yu] at heta
    rcases heta with ⟨hetaL, hetaU⟩
    constructor <;> linarith [hyBounds.1, hyBounds.2]
  have hvyCont : ContinuousOn (fun z : Point => partialY v z.1 z.2) K :=
    (continuousOn_uncurried_partialY_of_analyticOnNhd hv).mono hKsub
  obtain ⟨C, hC⟩ :=
    (isCompact_uIcc.prod isCompact_Icc).bddAbove_image hvyCont.norm
  have hsliceV : ∀ eta ∈ Set.Icc yl yu,
      ContinuousOn (fun s => v s eta) (Set.uIcc (0 : ℝ) x) := by
    intro eta heta s hs
    have hz : (s, eta) ∈ reconstructionBox rx ry := hKsub ⟨hs, heta⟩
    have hpath : ContinuousAt (fun t : ℝ => (t, eta)) s := by fun_prop
    have hc : ContinuousAt (fun t : ℝ => v t eta) s := by
      change ContinuousAt (uncurried v ∘ fun t : ℝ => (t, eta)) s
      exact ContinuousAt.comp_of_eq
        (f := fun t : ℝ => (t, eta)) (g := uncurried v)
        (hv (s, eta) hz).continuousAt hpath rfl
    exact hc.continuousWithinAt
  have hsliceVY : ∀ eta ∈ Set.Icc yl yu,
      ContinuousOn (fun s => partialY v s eta) (Set.uIcc (0 : ℝ) x) := by
    intro eta heta
    have hpath : Continuous (fun s : ℝ => (s, eta)) :=
      continuous_id.prodMk continuous_const
    simpa only [Function.comp_apply] using hvyCont.comp' hpath.continuousOn (by
      intro s hs
      exact ⟨hs, heta⟩)
  have hparam := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun eta s => v s eta)
    (F' := fun eta s => partialY v s eta)
    (μ := MeasureTheory.volume)
    (s := Set.Icc yl yu) (a := (0 : ℝ)) (b := x)
    (bound := fun _ => C)
    (Icc_mem_nhds hyl hyu)
    (by
      filter_upwards [Icc_mem_nhds hyl hyu] with eta heta
      exact ((hsliceV eta heta).mono Set.uIoc_subset_uIcc).aestronglyMeasurable
        measurableSet_uIoc)
    ((hsliceV y ⟨hyl.le, hyu.le⟩).intervalIntegrable)
    (((hsliceVY y ⟨hyl.le, hyu.le⟩).mono Set.uIoc_subset_uIcc).aestronglyMeasurable
      measurableSet_uIoc)
    (by
      exact Filter.Eventually.of_forall fun s hs eta heta => by
        apply hC
        refine ⟨(s, eta), ?_, rfl⟩
        change (s, eta) ∈ K
        exact ⟨Set.uIoc_subset_uIcc hs, heta⟩)
    intervalIntegrable_const
    (by
      exact Filter.Eventually.of_forall fun s hs eta heta => by
        have hz : (s, eta) ∈ reconstructionBox rx ry :=
          hKsub ⟨Set.uIoc_subset_uIcc hs, heta⟩
        have hpath : AnalyticAt ℝ (fun z : ℝ => (s, z)) eta :=
          analyticAt_const.prod analyticAt_id
        have ha : AnalyticAt ℝ (fun z => v s z) eta := by
          have ha' := (hv (s, eta) hz).comp hpath
          change AnalyticAt ℝ (fun z => v s z) eta at ha'
          exact ha'
        simpa only [partialY] using ha.differentiableAt.hasDerivAt)
  simpa only [reconstructedH, reconstructedHY] using hparam.2

/-- The fundamental theorem of calculus gives `h_x=v` for every continuous
`x`-slice. -/
theorem hasDerivAt_reconstructedH_x
    {v : ℝ → ℝ → ℝ} {x y : ℝ}
    (hv : Continuous (fun s => v s y)) :
    HasDerivAt (fun xi => reconstructedH v xi y) (v x y) x := by
  simpa only [reconstructedH] using
    intervalIntegral.integral_hasDerivAt_right
      (hv.intervalIntegrable 0 x)
      hv.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt

/-- The same FTC statement for the integrated `y` derivative. -/
theorem hasDerivAt_reconstructedHY_x
    {v : ℝ → ℝ → ℝ} {x y : ℝ}
    (hvy : Continuous (fun s => partialY v s y)) :
    HasDerivAt (fun xi => reconstructedHY v xi y) (partialY v x y) x := by
  simpa only [reconstructedHY] using
    intervalIntegral.integral_hasDerivAt_right
      (hvy.intervalIntegrable 0 x)
      hvy.aestronglyMeasurable.stronglyMeasurableAtFilter hvy.continuousAt

/-- Hence `gamma_x=v-1`. -/
theorem hasDerivAt_reconstructedGamma_x
    {v : ℝ → ℝ → ℝ} {x y : ℝ}
    (hv : Continuous (fun s => v s y)) :
    HasDerivAt (fun xi => reconstructedGamma v xi y) (v x y - 1) x := by
  have hraw := (hasDerivAt_reconstructedH_x hv).sub (hasDerivAt_id' x)
  apply hraw.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun _ => rfl

theorem partialX_reconstructedGamma
    {v : ℝ → ℝ → ℝ} {x y : ℝ}
    (hv : Continuous (fun s => v s y)) :
    partialX (reconstructedGamma v) x y = v x y - 1 := by
  exact (hasDerivAt_reconstructedGamma_x hv).deriv

/-! ## Explicit regularity package -/

/-- Sufficient data for reconstructing `gamma` from a reduced pair.

The `h_y` field is precisely the differentiation-under-the-integral witness.
For analytic reduced fields it follows from the usual locally dominated
parametric integral theorem.  Keeping it explicit makes the logical boundary
kernel-visible. -/
structure FirstOrderReconstructionData
    (v r : ℝ → ℝ → ℝ) : Prop where
  v_continuous_x : ∀ y, Continuous (fun x => v x y)
  vy_continuous_x : ∀ y, Continuous (fun x => partialY v x y)
  h_y : ∀ x y, HasDerivAt (fun eta => reconstructedH v x eta)
    (reconstructedHY v x y) y
  v_zero : ∀ y, v 0 y = 0
  r_zero : ∀ y, r 0 y = 0
  r_x : ∀ x y, HasDerivAt (fun xi => r xi y)
    (firstOrderRRate (firstOrderPhase y (v x y) (r x y))
      (partialY v x y)) x

/-- The local reconstruction package naturally produced by a convergent CK
series.  Unlike `FirstOrderReconstructionData`, it asks for no global
regularity witnesses: analyticity on a centered box automatically supplies
continuity of the two `x`-slices and differentiation under the parameter
integral.  The only equation stored here is the kinematic second reduced
equation, which is exactly what propagates `r = Gamma₂`. -/
structure AnalyticFirstOrderReconstructionData
    (v r : ℝ → ℝ → ℝ) (rx ry : ℝ) : Prop where
  rx_pos : 0 < rx
  ry_pos : 0 < ry
  v_analytic : AnalyticOnNhd ℝ (uncurried v) (reconstructionBox rx ry)
  r_analytic : AnalyticOnNhd ℝ (uncurried r) (reconstructionBox rx ry)
  v_zero : ∀ y, |y| < ry → v 0 y = 0
  r_zero : ∀ y, |y| < ry → r 0 y = 0
  r_equation : ∀ x y, |x| < rx → |y| < ry →
    deriv (fun xi => r xi y) x =
      firstOrderRRate (firstOrderPhase y (v x y) (r x y))
        (partialY v x y)

namespace AnalyticFirstOrderReconstructionData

variable {v r : ℝ → ℝ → ℝ} {rx ry : ℝ}

/-- Analyticity turns the stored derivative identity into the exact
`HasDerivAt` witness used by compatibility propagation. -/
theorem hasDerivAt_r_x
    (D : AnalyticFirstOrderReconstructionData v r rx ry)
    {x y : ℝ} (hx : |x| < rx) (hy : |y| < ry) :
    HasDerivAt (fun xi => r xi y)
      (firstOrderRRate (firstOrderPhase y (v x y) (r x y))
        (partialY v x y)) x := by
  have hpath : AnalyticAt ℝ (fun xi : ℝ => (xi, y)) x :=
    analyticAt_id.prod analyticAt_const
  have ha' : AnalyticAt ℝ
      (uncurried r ∘ fun xi : ℝ => (xi, y)) x :=
    AnalyticAt.comp_of_eq
      (f := fun xi : ℝ => (xi, y)) (g := uncurried r)
      (D.r_analytic (x, y) (mem_reconstructionBox.2 ⟨hx, hy⟩)) hpath rfl
  have ha : AnalyticAt ℝ (fun xi => r xi y) x := by
    unfold Function.comp uncurried at ha'
    exact ha'
  exact ha.differentiableAt.hasDerivAt.congr_deriv
    (D.r_equation x y hx hy)

/-- The evolution-variable FTC witness is automatic from local
analyticity. -/
theorem hasDerivAt_h_x
    (D : AnalyticFirstOrderReconstructionData v r rx ry)
    {x y : ℝ} (hx : |x| < rx) (hy : |y| < ry) :
    HasDerivAt (fun xi => reconstructedH v xi y) (v x y) x :=
  hasDerivAt_reconstructedH_x_of_analyticOnNhd D.v_analytic hx hy

/-- The evolution derivative of the integrated tangential derivative is
automatic from local analyticity. -/
theorem hasDerivAt_hy_x
    (D : AnalyticFirstOrderReconstructionData v r rx ry)
    {x y : ℝ} (hx : |x| < rx) (hy : |y| < ry) :
    HasDerivAt (fun xi => reconstructedHY v xi y) (partialY v x y) x :=
  hasDerivAt_reconstructedHY_x_of_analyticOnNhd D.v_analytic hx hy

/-- The differentiation-under-the-integral witness is not an extra
hypothesis for analytic data. -/
theorem hasDerivAt_h_y
    (D : AnalyticFirstOrderReconstructionData v r rx ry)
    {x y : ℝ} (hx : |x| < rx) (hy : |y| < ry) :
    HasDerivAt (fun eta => reconstructedH v x eta)
      (reconstructedHY v x y) y :=
  hasDerivAt_reconstructedH_y_of_analyticOnNhd D.v_analytic hx hy

/-- On the analytic box, `gamma_x=v-1`. -/
theorem hasDerivAt_gamma_x
    (D : AnalyticFirstOrderReconstructionData v r rx ry)
    {x y : ℝ} (hx : |x| < rx) (hy : |y| < ry) :
    HasDerivAt (fun xi => reconstructedGamma v xi y) (v x y - 1) x := by
  have hraw := (D.hasDerivAt_h_x hx hy).sub (hasDerivAt_id' x)
  apply hraw.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun _ => rfl

/-- The actual first partial of the reconstruction. -/
theorem partialX_gamma
    (D : AnalyticFirstOrderReconstructionData v r rx ry)
    {x y : ℝ} (hx : |x| < rx) (hy : |y| < ry) :
    partialX (reconstructedGamma v) x y = v x y - 1 :=
  (D.hasDerivAt_gamma_x hx hy).deriv

/-- The actual tangential partial of the reconstruction. -/
theorem partialY_gamma
    (D : AnalyticFirstOrderReconstructionData v r rx ry)
    {x y : ℝ} (hx : |x| < rx) (hy : |y| < ry) :
    partialY (reconstructedGamma v) x y = reconstructedHY v x y := by
  have hraw := (D.hasDerivAt_h_y hx hy).sub (hasDerivAt_const y x)
  have hraw' : HasDerivAt
      ((fun eta => reconstructedH v x eta) - fun _ => x)
      (reconstructedHY v x y) y := hraw.congr_deriv (by simp)
  have hfinal : HasDerivAt (fun eta => reconstructedGamma v x eta)
      (reconstructedHY v x y) y := by
    apply hraw'.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun _ => rfl
  exact hfinal.deriv

/-- The second reduced equation and zero row propagate the compatibility
constraint throughout the centered analytic box. -/
theorem r_eq_reconstructedH_sub_add
    (D : AnalyticFirstOrderReconstructionData v r rx ry)
    {x y : ℝ} (hx : |x| < rx) (hy : |y| < ry) :
    r x y = reconstructedH v x y - x + y * reconstructedHY v x y / 2 := by
  let G : ℝ → ℝ := fun s =>
    reconstructedH v s y - s + y * reconstructedHY v s y / 2
  let F : ℝ → ℝ := fun s => r s y - G s
  have hF : ∀ s ∈ Set.uIcc (0 : ℝ) x, HasDerivAt F 0 s := by
    intro s hs
    have hsx := abs_lt_of_mem_uIcc_zero hx hs
    have hh := D.hasDerivAt_h_x hsx hy
    have hhy := D.hasDerivAt_hy_x hsx hy
    have hbase := hh.sub (hasDerivAt_id' s)
    have hscaled := (hhy.const_mul y).div_const 2
    have hGraw := hbase.add hscaled
    have hG : HasDerivAt G
        (v s y - 1 + y * partialY v s y / 2) s := by
      apply hGraw.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall fun _ => rfl
    have hFraw := (D.hasDerivAt_r_x hsx hy).sub hG
    have hF' : HasDerivAt F
        (firstOrderRRate (firstOrderPhase y (v s y) (r s y))
          (partialY v s y) -
            (v s y - 1 + y * partialY v s y / 2)) s := by
      apply hFraw.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall fun _ => rfl
    apply hF'.congr_deriv
    simp [firstOrderRRate]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (continuous_const.intervalIntegrable (0 : ℝ) x)
  have hzero : F 0 = 0 := by
    simp [F, G, D.r_zero y hy]
  have htarget : F x = 0 := by
    have h := hFTC
    simp [hzero] at h
    linarith
  dsimp only [F, G] at htarget
  linarith

/-- Compatibility in the original `Gamma₂` form. -/
theorem r_eq_reconstructedGamma_add
    (D : AnalyticFirstOrderReconstructionData v r rx ry)
    {x y : ℝ} (hx : |x| < rx) (hy : |y| < ry) :
    r x y = reconstructedGamma v x y +
      y * partialY (reconstructedGamma v) x y / 2 := by
  rw [D.partialY_gamma hx hy]
  simpa only [reconstructedGamma] using D.r_eq_reconstructedH_sub_add hx hy

/-- The first reconstructed reduced field is the supplied `v`. -/
theorem firstOrderVField_gamma
    (D : AnalyticFirstOrderReconstructionData v r rx ry)
    {x y : ℝ} (hx : |x| < rx) (hy : |y| < ry) :
    firstOrderVField (reconstructedGamma v) x y = v x y := by
  unfold firstOrderVField
  rw [D.partialX_gamma hx hy]
  ring

/-- The second reconstructed reduced field is the supplied `r`. -/
theorem firstOrderRField_gamma
    (D : AnalyticFirstOrderReconstructionData v r rx ry)
    {x y : ℝ} (hx : |x| < rx) (hy : |y| < ry) :
    firstOrderRField (reconstructedGamma v) x y = r x y := by
  rw [firstOrderRField_eq]
  exact (D.r_eq_reconstructedGamma_add hx hy).symm

/-- The reconstructed and supplied phases agree throughout the box. -/
theorem firstOrderFieldPhase_gamma
    (D : AnalyticFirstOrderReconstructionData v r rx ry)
    {x y : ℝ} (hx : |x| < rx) (hy : |y| < ry) :
    firstOrderFieldPhase (reconstructedGamma v) x y =
      firstOrderPhase y (v x y) (r x y) := by
  unfold firstOrderFieldPhase
  rw [D.firstOrderVField_gamma hx hy, D.firstOrderRField_gamma hx hy]

/-- Local identification of the first reduced field along an `x`-slice. -/
theorem eventuallyEq_firstOrderVField_x
    (D : AnalyticFirstOrderReconstructionData v r rx ry)
    {x y : ℝ} (hx : |x| < rx) (hy : |y| < ry) :
    (fun xi => firstOrderVField (reconstructedGamma v) xi y) =ᶠ[nhds x]
      (fun xi => v xi y) := by
  filter_upwards [isOpen_Ioo.mem_nhds (abs_lt.mp hx)] with xi hxi
  exact D.firstOrderVField_gamma (abs_lt.mpr hxi) hy

/-- Local identification of the first reduced field along a `y`-slice. -/
theorem eventuallyEq_firstOrderVField_y
    (D : AnalyticFirstOrderReconstructionData v r rx ry)
    {x y : ℝ} (hx : |x| < rx) (hy : |y| < ry) :
    (fun eta => firstOrderVField (reconstructedGamma v) x eta) =ᶠ[nhds y]
      (fun eta => v x eta) := by
  filter_upwards [isOpen_Ioo.mem_nhds (abs_lt.mp hy)] with eta heta
  exact D.firstOrderVField_gamma hx (abs_lt.mpr heta)

/-- Local identification of the second reduced field along an `x`-slice. -/
theorem eventuallyEq_firstOrderRField_x
    (D : AnalyticFirstOrderReconstructionData v r rx ry)
    {x y : ℝ} (hx : |x| < rx) (hy : |y| < ry) :
    (fun xi => firstOrderRField (reconstructedGamma v) xi y) =ᶠ[nhds x]
      (fun xi => r xi y) := by
  filter_upwards [isOpen_Ioo.mem_nhds (abs_lt.mp hx)] with xi hxi
  exact D.firstOrderRField_gamma (abs_lt.mpr hxi) hy

/-- Local identification of the second reduced field along a `y`-slice. -/
theorem eventuallyEq_firstOrderRField_y
    (D : AnalyticFirstOrderReconstructionData v r rx ry)
    {x y : ℝ} (hx : |x| < rx) (hy : |y| < ry) :
    (fun eta => firstOrderRField (reconstructedGamma v) x eta) =ᶠ[nhds y]
      (fun eta => r x eta) := by
  filter_upwards [isOpen_Ioo.mem_nhds (abs_lt.mp hy)] with eta heta
  exact D.firstOrderRField_gamma hx (abs_lt.mpr heta)

/-- The zero rows give the original Cauchy data on the whole tangential
interval of the analytic box. -/
theorem reconstructedGamma_hasCauchyDataOn
    (D : AnalyticFirstOrderReconstructionData v r rx ry) :
    HasCauchyDataOn (reconstructedGamma v) ry := by
  intro y hy
  have hx0 : |(0 : ℝ)| < rx := by simpa using D.rx_pos
  constructor
  · exact reconstructedGamma_zero v y
  · have hv := D.firstOrderVField_gamma hx0 hy
    unfold firstOrderVField at hv
    rw [D.v_zero y hy] at hv
    linarith

end AnalyticFirstOrderReconstructionData

/-- The explicit parameter-integral witness identifies the actual `y`
derivative of `h`. -/
theorem partialY_reconstructedH
    {v r : ℝ → ℝ → ℝ}
    (D : FirstOrderReconstructionData v r) (x y : ℝ) :
    partialY (reconstructedH v) x y = reconstructedHY v x y := by
  exact (D.h_y x y).deriv

/-- Since subtracting `x` is constant in the `y` variable, the same formula
holds for `gamma_y`. -/
theorem partialY_reconstructedGamma
    {v r : ℝ → ℝ → ℝ}
    (D : FirstOrderReconstructionData v r) (x y : ℝ) :
    partialY (reconstructedGamma v) x y = reconstructedHY v x y := by
  have hraw := (D.h_y x y).sub (hasDerivAt_const y x)
  have hraw' : HasDerivAt
      ((fun eta => reconstructedH v x eta) - fun _ => x)
      (reconstructedHY v x y) y := hraw.congr_deriv (by simp)
  have hfinal : HasDerivAt (fun eta => reconstructedGamma v x eta)
      (reconstructedHY v x y) y := by
    apply hraw'.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun _ => rfl
  exact hfinal.deriv

/-! ## Propagation of the compatibility constraint -/

/-- The zero data and the second reduced equation force
`r=h-x+(y/2)h_y`.  The proof differentiates the defect in `x` and applies the
fundamental theorem of calculus on the segment from `0` to `x`. -/
theorem r_eq_reconstructedH_sub_add
    {v r : ℝ → ℝ → ℝ}
    (D : FirstOrderReconstructionData v r) (x y : ℝ) :
    r x y = reconstructedH v x y - x + y * reconstructedHY v x y / 2 := by
  let G : ℝ → ℝ := fun s =>
    reconstructedH v s y - s + y * reconstructedHY v s y / 2
  let F : ℝ → ℝ := fun s => r s y - G s
  have hF : ∀ s ∈ Set.uIcc (0 : ℝ) x, HasDerivAt F 0 s := by
    intro s _hs
    have hh := hasDerivAt_reconstructedH_x (D.v_continuous_x y)
      (x := s)
    have hhy := hasDerivAt_reconstructedHY_x (D.vy_continuous_x y)
      (x := s)
    have hbase := hh.sub (hasDerivAt_id' s)
    have hscaled := (hhy.const_mul y).div_const 2
    have hGraw := hbase.add hscaled
    have hG : HasDerivAt G
        (v s y - 1 + y * partialY v s y / 2) s := by
      apply hGraw.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall fun _ => rfl
    have hFraw := (D.r_x s y).sub hG
    have hF' : HasDerivAt F
        (firstOrderRRate (firstOrderPhase y (v s y) (r s y))
          (partialY v s y) -
            (v s y - 1 + y * partialY v s y / 2)) s := by
      apply hFraw.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall fun _ => rfl
    apply hF'.congr_deriv
    simp [firstOrderRRate]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (continuous_const.intervalIntegrable (0 : ℝ) x)
  have hzero : F 0 = 0 := by
    simp [F, G, D.r_zero]
  have htarget : F x = 0 := by
    have h := hFTC
    simp [hzero] at h
    linarith
  dsimp only [F, G] at htarget
  linarith

/-- Compatibility in the exact original form
`r=gamma+(y/2)gamma_y`. -/
theorem r_eq_reconstructedGamma_add
    {v r : ℝ → ℝ → ℝ}
    (D : FirstOrderReconstructionData v r) (x y : ℝ) :
    r x y = reconstructedGamma v x y +
      y * partialY (reconstructedGamma v) x y / 2 := by
  rw [partialY_reconstructedGamma D]
  simpa only [reconstructedGamma] using r_eq_reconstructedH_sub_add D x y

/-! ## Identification of the reconstructed reduced fields -/

/-- Reconstructing and then taking the first reduced field returns `v`. -/
theorem firstOrderVField_reconstructedGamma
    {v r : ℝ → ℝ → ℝ}
    (D : FirstOrderReconstructionData v r) (x y : ℝ) :
    firstOrderVField (reconstructedGamma v) x y = v x y := by
  unfold firstOrderVField
  rw [partialX_reconstructedGamma (D.v_continuous_x y)]
  ring

/-- Reconstructing and then taking `Gamma₂` returns `r`. -/
theorem firstOrderRField_reconstructedGamma
    {v r : ℝ → ℝ → ℝ}
    (D : FirstOrderReconstructionData v r) (x y : ℝ) :
    firstOrderRField (reconstructedGamma v) x y = r x y := by
  rw [firstOrderRField_eq]
  exact (r_eq_reconstructedGamma_add D x y).symm

/-- The reconstructed coefficient phase is the supplied reduced phase. -/
theorem firstOrderFieldPhase_reconstructedGamma
    {v r : ℝ → ℝ → ℝ}
    (D : FirstOrderReconstructionData v r) (x y : ℝ) :
    firstOrderFieldPhase (reconstructedGamma v) x y =
      firstOrderPhase y (v x y) (r x y) := by
  unfold firstOrderFieldPhase
  rw [firstOrderVField_reconstructedGamma D,
    firstOrderRField_reconstructedGamma D]

/-! ## Transfer of the reduced PDE -/

/-- The dynamic first equation for independently supplied reduced fields.
The second equation is already a field of `FirstOrderReconstructionData`
because it is what propagates the compatibility constraint. -/
def ReducedFirstOrderFirstEquationAt
    (P : Params) (v r : ℝ → ℝ → ℝ) (x y : ℝ) : Prop :=
  deriv (fun xi => v xi y) x =
    firstOrderVRate P (firstOrderPhase y (v x y) (r x y))
      (partialY v x y) (partialY r x y)

/-- The actual two-equation reduced PDE for independently supplied fields
`v` and `r`. -/
def ReducedFirstOrderSystemAt
    (P : Params) (v r : ℝ → ℝ → ℝ) (x y : ℝ) : Prop :=
  deriv (fun xi => v xi y) x =
      firstOrderVRate P (firstOrderPhase y (v x y) (r x y))
        (partialY v x y) (partialY r x y) ∧
    deriv (fun xi => r xi y) x =
      firstOrderRRate (firstOrderPhase y (v x y) (r x y))
        (partialY v x y)

namespace AnalyticFirstOrderReconstructionData

variable {v r : ℝ → ℝ → ℝ} {rx ry : ℝ}

/-- The local analytic reconstruction package supplies the kinematic
equation, so the dynamic first equation gives the full reduced system. -/
theorem reducedFirstOrderSystemAt_of_firstEquation
    (P : Params) (D : AnalyticFirstOrderReconstructionData v r rx ry)
    {x y : ℝ} (hx : |x| < rx) (hy : |y| < ry)
    (hfirst : ReducedFirstOrderFirstEquationAt P v r x y) :
    ReducedFirstOrderSystemAt P v r x y := by
  exact ⟨hfirst, D.r_equation x y hx hy⟩

/-- On the centered box, the actual reconstructed system is exactly the
independently supplied reduced system.  Local eventual equalities suffice
for all four derivatives, so no global extension of the CK field is needed. -/
theorem firstOrderSystemAt_gamma_iff
    (P : Params) (D : AnalyticFirstOrderReconstructionData v r rx ry)
    {x y : ℝ} (hx : |x| < rx) (hy : |y| < ry) :
    FirstOrderSystemAt P (reconstructedGamma v) x y ↔
      ReducedFirstOrderSystemAt P v r x y := by
  have hvx := D.eventuallyEq_firstOrderVField_x hx hy
  have hvy := D.eventuallyEq_firstOrderVField_y hx hy
  have hrx := D.eventuallyEq_firstOrderRField_x hx hy
  have hry := D.eventuallyEq_firstOrderRField_y hx hy
  unfold FirstOrderSystemAt ReducedFirstOrderSystemAt partialY
  rw [hvx.deriv_eq, hvy.deriv_eq, hrx.deriv_eq, hry.deriv_eq,
    D.firstOrderFieldPhase_gamma hx hy]

/-- Pointwise transfer from the local analytic reduced system to the
original auxiliary equation. -/
theorem auxiliaryEquationAt_gamma
    (P : Params) (D : AnalyticFirstOrderReconstructionData v r rx ry)
    {x y : ℝ} (hx : |x| < rx) (hy : |y| < ry)
    (hreg : GammaDifferentialDataAt (reconstructedGamma v) x y)
    (hcoeff0 : firstOrderCoeff0 P
      (firstOrderPhase y (v x y) (r x y)) ≠ 0)
    (hsys : ReducedFirstOrderSystemAt P v r x y) :
    auxiliaryEquationAt P (reconstructedGamma v) x y := by
  have hphase := D.firstOrderFieldPhase_gamma hx hy
  have hcoeff0' : firstOrderCoeff0 P
      (firstOrderFieldPhase (reconstructedGamma v) x y) ≠ 0 := by
    rw [hphase]
    exact hcoeff0
  apply auxiliaryEquationAt_of_firstOrderSystemAt P hreg hcoeff0'
  exact (D.firstOrderSystemAt_gamma_iff P hx hy).2 hsys

/-- Analyticity of the reconstructed primitive discharges its complete
pointwise `C²` differential package. -/
theorem auxiliaryEquationAt_gamma_of_analyticAt
    (P : Params) (D : AnalyticFirstOrderReconstructionData v r rx ry)
    {x y : ℝ} (hx : |x| < rx) (hy : |y| < ry)
    (hgamma : AnalyticAt ℝ (uncurried (reconstructedGamma v)) (x, y))
    (hcoeff0 : firstOrderCoeff0 P
      (firstOrderPhase y (v x y) (r x y)) ≠ 0)
    (hsys : ReducedFirstOrderSystemAt P v r x y) :
    auxiliaryEquationAt P (reconstructedGamma v) x y :=
  D.auxiliaryEquationAt_gamma P hx hy
    (gammaDifferentialDataAt_of_analyticAt hgamma) hcoeff0 hsys

/-- Convenient local analytic form requiring only the dynamic first
equation; the second equation is already part of `D`. -/
theorem auxiliaryEquationAt_gamma_of_analyticAt_firstEquation
    (P : Params) (D : AnalyticFirstOrderReconstructionData v r rx ry)
    {x y : ℝ} (hx : |x| < rx) (hy : |y| < ry)
    (hgamma : AnalyticAt ℝ (uncurried (reconstructedGamma v)) (x, y))
    (hcoeff0 : firstOrderCoeff0 P
      (firstOrderPhase y (v x y) (r x y)) ≠ 0)
    (hfirst : ReducedFirstOrderFirstEquationAt P v r x y) :
    auxiliaryEquationAt P (reconstructedGamma v) x y :=
  D.auxiliaryEquationAt_gamma_of_analyticAt P hx hy hgamma hcoeff0
    (D.reducedFirstOrderSystemAt_of_firstEquation P hx hy hfirst)

end AnalyticFirstOrderReconstructionData

/-- Reconstruction data supply the second reduced equation, so only the
dynamic first equation remains to be checked. -/
theorem reducedFirstOrderSystemAt_of_firstEquation
    (P : Params) {v r : ℝ → ℝ → ℝ}
    (D : FirstOrderReconstructionData v r) {x y : ℝ}
    (hfirst : ReducedFirstOrderFirstEquationAt P v r x y) :
    ReducedFirstOrderSystemAt P v r x y := by
  exact ⟨hfirst, (D.r_x x y).deriv⟩

/-- Under reconstruction data, the independently stated reduced system is
exactly `FirstOrderSystemAt` for the reconstructed `gamma`. -/
theorem firstOrderSystemAt_reconstructedGamma_iff
    (P : Params) {v r : ℝ → ℝ → ℝ}
    (D : FirstOrderReconstructionData v r) (x y : ℝ) :
    FirstOrderSystemAt P (reconstructedGamma v) x y ↔
      ReducedFirstOrderSystemAt P v r x y := by
  have hvx : (fun xi => firstOrderVField (reconstructedGamma v) xi y) =
      (fun xi => v xi y) := by
    funext xi
    exact firstOrderVField_reconstructedGamma D xi y
  have hvy : (fun eta => firstOrderVField (reconstructedGamma v) x eta) =
      v x := by
    funext eta
    exact firstOrderVField_reconstructedGamma D x eta
  have hrx : (fun xi => firstOrderRField (reconstructedGamma v) xi y) =
      (fun xi => r xi y) := by
    funext xi
    exact firstOrderRField_reconstructedGamma D xi y
  have hry : (fun eta => firstOrderRField (reconstructedGamma v) x eta) =
      r x := by
    funext eta
    exact firstOrderRField_reconstructedGamma D x eta
  unfold FirstOrderSystemAt ReducedFirstOrderSystemAt
  rw [hvx, hvy, hrx, hry,
    firstOrderFieldPhase_reconstructedGamma D]
  rfl

/-- The first reduced equation therefore implies the original auxiliary PDE
once the reconstructed function has the pointwise `C²` data required by the
actual-function bridge. -/
theorem auxiliaryEquationAt_reconstructedGamma
    (P : Params) {v r : ℝ → ℝ → ℝ}
    (D : FirstOrderReconstructionData v r) {x y : ℝ}
    (hreg : GammaDifferentialDataAt (reconstructedGamma v) x y)
    (hcoeff0 : firstOrderCoeff0 P
      (firstOrderPhase y (v x y) (r x y)) ≠ 0)
    (hsys : ReducedFirstOrderSystemAt P v r x y) :
    auxiliaryEquationAt P (reconstructedGamma v) x y := by
  have hphase := firstOrderFieldPhase_reconstructedGamma D x y
  have hcoeff0' : firstOrderCoeff0 P
      (firstOrderFieldPhase (reconstructedGamma v) x y) ≠ 0 := by
    rw [hphase]
    exact hcoeff0
  apply auxiliaryEquationAt_of_firstOrderSystemAt P hreg hcoeff0'
  exact (firstOrderSystemAt_reconstructedGamma_iff P D x y).2 hsys

/-- Convenient form requiring only the dynamic first equation; the
kinematic second equation is taken from the reconstruction data. -/
theorem auxiliaryEquationAt_reconstructedGamma_of_firstEquation
    (P : Params) {v r : ℝ → ℝ → ℝ}
    (D : FirstOrderReconstructionData v r) {x y : ℝ}
    (hreg : GammaDifferentialDataAt (reconstructedGamma v) x y)
    (hcoeff0 : firstOrderCoeff0 P
      (firstOrderPhase y (v x y) (r x y)) ≠ 0)
    (hfirst : ReducedFirstOrderFirstEquationAt P v r x y) :
    auxiliaryEquationAt P (reconstructedGamma v) x y := by
  exact auxiliaryEquationAt_reconstructedGamma P D hreg hcoeff0
    (reducedFirstOrderSystemAt_of_firstEquation P D hfirst)

/-- If the reconstructed function is analytic, its pointwise differential
hypotheses are automatic. -/
theorem auxiliaryEquationAt_reconstructedGamma_of_analyticAt
    (P : Params) {v r : ℝ → ℝ → ℝ}
    (D : FirstOrderReconstructionData v r) {x y : ℝ}
    (hgamma : AnalyticAt ℝ (uncurried (reconstructedGamma v)) (x, y))
    (hcoeff0 : firstOrderCoeff0 P
      (firstOrderPhase y (v x y) (r x y)) ≠ 0)
    (hsys : ReducedFirstOrderSystemAt P v r x y) :
    auxiliaryEquationAt P (reconstructedGamma v) x y := by
  exact auxiliaryEquationAt_reconstructedGamma P D
    (gammaDifferentialDataAt_of_analyticAt hgamma) hcoeff0 hsys

/-- Analytic reconstructed version requiring only the dynamic first
equation. -/
theorem auxiliaryEquationAt_reconstructedGamma_of_analyticAt_firstEquation
    (P : Params) {v r : ℝ → ℝ → ℝ}
    (D : FirstOrderReconstructionData v r) {x y : ℝ}
    (hgamma : AnalyticAt ℝ (uncurried (reconstructedGamma v)) (x, y))
    (hcoeff0 : firstOrderCoeff0 P
      (firstOrderPhase y (v x y) (r x y)) ≠ 0)
    (hfirst : ReducedFirstOrderFirstEquationAt P v r x y) :
    auxiliaryEquationAt P (reconstructedGamma v) x y := by
  exact auxiliaryEquationAt_reconstructedGamma_of_firstEquation P D
    (gammaDifferentialDataAt_of_analyticAt hgamma) hcoeff0 hfirst

/-! ## Cauchy data -/

/-- The zero reduced data give exactly the original Cauchy data
`gamma(0,y)=0`, `gamma_x(0,y)=-1`. -/
theorem reconstructedGamma_hasCauchyDataOn
    {v r : ℝ → ℝ → ℝ}
    (D : FirstOrderReconstructionData v r) (radius : ℝ) :
    HasCauchyDataOn (reconstructedGamma v) radius := by
  intro y _hy
  constructor
  · exact reconstructedGamma_zero v y
  · have hv := firstOrderVField_reconstructedGamma D 0 y
    unfold firstOrderVField at hv
    rw [D.v_zero y] at hv
    linarith

/-- Combined pointwise PDE reconstruction and Cauchy-data conclusion. -/
theorem reconstructedGamma_auxiliaryEquationAt_and_cauchyData
    (P : Params) {v r : ℝ → ℝ → ℝ}
    (D : FirstOrderReconstructionData v r) {x y radius : ℝ}
    (hgamma : AnalyticAt ℝ (uncurried (reconstructedGamma v)) (x, y))
    (hcoeff0 : firstOrderCoeff0 P
      (firstOrderPhase y (v x y) (r x y)) ≠ 0)
    (hsys : ReducedFirstOrderSystemAt P v r x y) :
    auxiliaryEquationAt P (reconstructedGamma v) x y ∧
      HasCauchyDataOn (reconstructedGamma v) radius := by
  exact ⟨auxiliaryEquationAt_reconstructedGamma_of_analyticAt P D
      hgamma hcoeff0 hsys,
    reconstructedGamma_hasCauchyDataOn D radius⟩

end

end StressTensor
