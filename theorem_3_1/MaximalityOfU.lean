import Mathlib

/-!
# Maximality across a light ray

This file formalizes the reusable core of Section 3.3, "Maximality of `u`".
The analytic Cauchy--Kowalevskaya construction from the preceding section is deliberately an input.
-/

open Filter MeasureTheory Metric Set Topology

noncomputable section

namespace MaximalityOfU

/-! ## Exponents -/

/-- The Holder-conjugate exponent used in the paper: `p = q / (q - 1)`. -/
def conjugateExponent (q : ℝ) : ℝ := q / (q - 1)

/-- Exponent of the tangential stress singularity. -/
def singularityExponent (p : ℝ) : ℝ := 2 / p

/-- Exponent governing decay of the normal stress. -/
def decayExponent (p : ℝ) : ℝ := 1 - 2 / p

/-- The weak-Lp exponent associated with a `|y|^(-2/p)` singularity. -/
def weakExponent (p : ℝ) : ℝ := p / 2

theorem conjugateExponent_gt_two {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2) :
    2 < conjugateExponent q := by
  rw [conjugateExponent, lt_div_iff₀ (sub_pos.mpr hq1)]
  linarith

theorem singularityExponent_mem_Ioo {p : ℝ} (hp : 2 < p) :
    singularityExponent p ∈ Ioo (0 : ℝ) 1 := by
  have hp0 : 0 < p := by linarith
  constructor
  · exact div_pos (by norm_num) hp0
  · exact (div_lt_one hp0).2 hp

theorem decayExponent_pos {p : ℝ} (hp : 2 < p) : 0 < decayExponent p := by
  have h := (singularityExponent_mem_Ioo hp).2
  rw [decayExponent, singularityExponent] at *
  linarith

theorem weakExponent_gt_one {p : ℝ} (hp : 2 < p) : 1 < weakExponent p := by
  rw [weakExponent]
  linarith

theorem weakExponent_eq_inv_singularity {p : ℝ} (hp : 2 < p) :
    weakExponent p = (singularityExponent p)⁻¹ := by
  have hp0 : p ≠ 0 := by linarith
  rw [weakExponent, singularityExponent]
  field_simp

theorem weakExponent_conjugate {q : ℝ} (hq1 : 1 < q) :
    weakExponent (conjugateExponent q) = q / (2 * (q - 1)) := by
  have hq : q - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
  rw [weakExponent, conjugateExponent]
  field_simp

/-! ## Algebraic ansatz and stress representative -/

abbrev Point := ℝ × ℝ
abbrev Vector2 := EuclideanSpace ℝ (Fin 2)

/-- The ansatz `u(x,y) = x + y^2 gamma(x,y)` from (3.1). -/
def ansatz (gamma : Point → ℝ) (z : Point) : ℝ :=
  z.1 + z.2 ^ 2 * gamma z

/-- `Gamma_1`, with `dxGamma` standing for `partial_x gamma`. -/
def Gamma1 (dxGamma : Point → ℝ) (z : Point) : ℝ :=
  1 + z.2 ^ 2 * dxGamma z

/-- `Gamma_2`, with `dyGamma` standing for `partial_y gamma`. -/
def Gamma2 (gamma dyGamma : Point → ℝ) (z : Point) : ℝ :=
  gamma z + z.2 * dyGamma z / 2

/-- `Gamma_0` from the identity `|Du|^2 = 1 + y^2 Gamma_0`. -/
def Gamma0 (gamma dxGamma dyGamma : Point → ℝ) (z : Point) : ℝ :=
  2 * dxGamma z + z.2 ^ 2 * (dxGamma z) ^ 2 + 4 * (Gamma2 gamma dyGamma z) ^ 2

theorem formalGradientNormSq (gamma dxGamma dyGamma : Point → ℝ) (z : Point) :
    (Gamma1 dxGamma z) ^ 2 + (2 * z.2 * Gamma2 gamma dyGamma z) ^ 2 =
      1 + z.2 ^ 2 * Gamma0 gamma dxGamma dyGamma z := by
  simp only [Gamma0, Gamma1]
  ring

/-- A total representative of the factorized stress (3.10), set to zero on the light ray. -/
def stressRepresentative (p : ℝ) (S Gamma1' Gamma2' : Point → ℝ) (z : Point) : Vector2 :=
  if z.2 = 0 then 0
  else (EuclideanSpace.equiv (Fin 2) ℝ).symm
    ![|z.2| ^ (-2 / p) * S z * Gamma1' z,
      2 * z.2 * |z.2| ^ (-2 / p) * S z * Gamma2' z]

@[simp]
theorem stressRepresentative_on_axis (p : ℝ) (S Gamma1' Gamma2' : Point → ℝ) (x : ℝ) :
    stressRepresentative p S Gamma1' Gamma2' (x, 0) = 0 := by
  simp [stressRepresentative]

/-! ## Geometry and weak-tail estimate -/

/-- The open square `(-ell,ell)^2`. -/
def cube (ell : ℝ) : Set Point := Ioo (-ell) ell ×ˢ Ioo (-ell) ell

/-- The horizontal light segment. -/
def lightRay (ell : ℝ) : Set Point := Icc (-ell) ell ×ˢ ({0} : Set ℝ)

/-- The central strip removed in the excision argument. -/
def centralStrip (ell delta : ℝ) : Set Point := Ioo (-ell) ell ×ˢ Ioo (-delta) delta

theorem cube_measurable (ell : ℝ) : MeasurableSet (cube ell) :=
  measurableSet_Ioo.prod measurableSet_Ioo

theorem lightRay_volume (ell : ℝ) : volume (lightRay ell) = 0 := by
  rw [lightRay, Measure.volume_eq_prod, Measure.prod_prod]
  simp

theorem centralStrip_volume {ell : ℝ} (hell : 0 ≤ ell) (delta : ℝ) :
    volume (centralStrip ell delta) = ENNReal.ofReal (4 * ell * delta) := by
  rw [centralStrip, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo,
    Real.volume_Ioo]
  have heq1 : ell - -ell = 2 * ell := by ring
  have heq2 : delta - -delta = 2 * delta := by ring
  rw [heq1, heq2]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * ell)]
  congr 1
  ring

theorem centralStrip_measureReal {ell delta : ℝ} (hell : 0 ≤ ell) (hdelta : 0 ≤ delta) :
    volume.real (centralStrip ell delta) = 4 * ell * delta := by
  rw [centralStrip, Measure.volume_eq_prod, measureReal_prod_prod]
  rw [Real.volume_real_Ioo_of_le (by linarith),
    Real.volume_real_Ioo_of_le (by linarith)]
  ring

theorem centralStrip_volume_tendsto_zero {ell : ℝ} (hell : 0 ≤ ell) :
    Tendsto (fun delta : ℝ => volume (centralStrip ell delta)) (𝓝[>] 0) (𝓝 0) := by
  have hcont : Continuous (fun delta : ℝ => ENNReal.ofReal (4 * ell * delta)) :=
    ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)
  have hfull : Tendsto (fun delta : ℝ => ENNReal.ofReal (4 * ell * delta))
      (𝓝 0) (𝓝 0) := by
    simpa using hcont.tendsto 0
  have hlim : Tendsto (fun delta : ℝ => ENNReal.ofReal (4 * ell * delta))
      (𝓝[>] 0) (𝓝 0) := by
    exact hfull.mono_left nhdsWithin_le_nhds
  exact hlim.congr' (Eventually.of_forall fun delta => (centralStrip_volume hell delta).symm)

theorem integrableOn_abs_rpow_neg_Ioo {a ell : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (_hell : 0 < ell) :
    IntegrableOn (fun y : ℝ => |y| ^ (-a)) (Ioo (-ell) ell) volume := by
  have hmeas : AEStronglyMeasurable (fun y : ℝ => |y| ^ (-a)) volume := by
    apply Measurable.aestronglyMeasurable
    apply measurable_of_continuousOn_compl_singleton 0
    intro y hy
    have hy0 : y ≠ 0 := by simpa using hy
    exact (continuous_abs.continuousAt.rpow_const
      (Or.inl (abs_ne_zero.mpr hy0))).continuousWithinAt
  have hball : IntegrableOn (fun y : ℝ => |y| ^ (-a)) (ball 0 ell) volume := by
    refine integrableOn_ball_of_norm_le_rpow (E := ℝ) (F := ℝ)
      (μ := volume) (C := 1) (α := a) (r := ell) (by simp) ?_ ?_ hmeas
    · simpa using ha.2
    · filter_upwards with y
      simp only [Real.norm_eq_abs, one_mul]
      rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) (-a))]
  simpa [Real.ball_eq_Ioo] using hball

theorem integrableOn_snd_abs_rpow_neg_cube {a ell : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hell : 0 < ell) :
    IntegrableOn (fun z : Point => |z.2| ^ (-a)) (cube ell) volume := by
  have hy := integrableOn_abs_rpow_neg_Ioo (a := a) (ell := ell) ha hell
  have hprod : Integrable (fun z : Point => |z.2| ^ (-a))
      ((volume.restrict (Ioo (-ell) ell)).prod
        (volume.restrict (Ioo (-ell) ell))) :=
    hy.comp_snd (volume.restrict (Ioo (-ell) ell))
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hprod
  exact hprod

theorem integrableOn_cube_of_norm_le_snd_rpow {E : Type*} [NormedAddCommGroup E]
    {a ell c : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hell : 0 < ell) {F : Point → E}
    (hmeas : AEStronglyMeasurable F (volume.restrict (cube ell)))
    (hbound : ∀ᵐ z ∂(volume.restrict (cube ell)),
      ‖F z‖ ≤ c * |z.2| ^ (-a)) :
    IntegrableOn F (cube ell) volume := by
  have hmajor := (integrableOn_snd_abs_rpow_neg_cube ha hell).const_mul c
  exact hmajor.mono' hmeas hbound

theorem stress_integrableOn_cube_of_power_bound {E : Type*} [NormedAddCommGroup E]
    {p ell c : ℝ} (hp : 2 < p) (hell : 0 < ell) {F : Point → E}
    (hmeas : AEStronglyMeasurable F (volume.restrict (cube ell)))
    (hbound : ∀ᵐ z ∂(volume.restrict (cube ell)),
      ‖F z‖ ≤ c * |z.2| ^ (-singularityExponent p)) :
    IntegrableOn F (cube ell) volume :=
  integrableOn_cube_of_norm_le_snd_rpow (singularityExponent_mem_Ioo hp) hell hmeas hbound

theorem stress_zeroExtension_integrable_of_power_bound {E : Type*} [NormedAddCommGroup E]
    {p ell c : ℝ} (hp : 2 < p) (hell : 0 < ell) {F : Point → E}
    (hmeas : AEStronglyMeasurable F (volume.restrict (cube ell)))
    (hbound : ∀ᵐ z ∂(volume.restrict (cube ell)),
      ‖F z‖ ≤ c * |z.2| ^ (-singularityExponent p)) :
    Integrable ((cube ell).indicator F) volume :=
  (stress_integrableOn_cube_of_power_bound hp hell hmeas hbound).integrable_indicator
    (cube_measurable ell)

/-- Superlevel set of `F`, restricted to `domain`. -/
def superlevelOn {E : Type*} [Norm E] (domain : Set Point) (F : Point → E) (lambda : ℝ) :
    Set Point := {z | z ∈ domain ∧ lambda < ‖F z‖}

/--
Distribution-function formulation of membership in weak `L^r` on a
finite-measure domain.  The finiteness conjunct is essential: without it,
`Measure.real` would turn an infinite superlevel measure into zero.
-/
def HasWeakLpTailOn {Omega E : Type*} [MeasurableSpace Omega] [Norm E]
    (mu : Measure Omega) (r : ℝ) (domain : Set Omega) (F : Omega → E) : Prop :=
  mu domain ≠ ⊤ ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ lambda : ℝ, 0 < lambda →
    lambda ^ r * mu.real {x | x ∈ domain ∧ lambda < ‖F x‖} ≤ K

theorem weakTail_of_distribution_bound {Omega E : Type*} [MeasurableSpace Omega] [Norm E]
    {mu : Measure Omega} {r K : ℝ} {domain : Set Omega} {F : Omega → E}
    (hfinite : mu domain ≠ ⊤)
    (hK : 0 ≤ K)
    (hbound : ∀ lambda : ℝ, 0 < lambda →
      mu.real {x | x ∈ domain ∧ lambda < ‖F x‖} ≤ K / lambda ^ r) :
    HasWeakLpTailOn mu r domain F := by
  refine ⟨hfinite, K, hK, fun lambda hlambda => ?_⟩
  have hpow : 0 < lambda ^ r := Real.rpow_pos_of_pos hlambda r
  calc
    lambda ^ r * mu.real {x | x ∈ domain ∧ lambda < ‖F x‖} ≤
        lambda ^ r * (K / lambda ^ r) :=
      mul_le_mul_of_nonneg_left (hbound lambda hlambda) hpow.le
    _ = K := by field_simp

theorem weakTail_of_superlevel_subset_strip {E : Type*} [Norm E]
    {ell c r : ℝ} (hell : 0 ≤ ell) (hc : 0 ≤ c) (_hr : 0 < r) (F : Point → E)
    (hsubset : ∀ lambda : ℝ, 0 < lambda →
      superlevelOn (cube ell) F lambda ⊆ centralStrip ell ((c / lambda) ^ r)) :
    HasWeakLpTailOn volume r (cube ell) F := by
  let K : ℝ := 4 * ell * c ^ r
  have hfiniteCube : volume (cube ell) ≠ ⊤ := by
    rw [cube, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  refine ⟨hfiniteCube, K, by dsimp [K]; positivity, fun lambda hlambda => ?_⟩
  change lambda ^ r * volume.real (superlevelOn (cube ell) F lambda) ≤ K
  have hwidth : 0 ≤ (c / lambda) ^ r :=
    Real.rpow_nonneg (div_nonneg hc hlambda.le) r
  have hfinite : volume (centralStrip ell ((c / lambda) ^ r)) ≠ ⊤ := by
    rw [centralStrip_volume hell]
    exact ENNReal.ofReal_ne_top
  have hmeasure : volume.real (superlevelOn (cube ell) F lambda) ≤
      volume.real (centralStrip ell ((c / lambda) ^ r)) :=
    measureReal_mono (hsubset lambda hlambda) hfinite
  rw [centralStrip_measureReal hell hwidth] at hmeasure
  calc
    lambda ^ r * volume.real (superlevelOn (cube ell) F lambda) ≤
        lambda ^ r * (4 * ell * (c / lambda) ^ r) :=
      mul_le_mul_of_nonneg_left hmeasure (Real.rpow_nonneg hlambda.le r)
    _ = K := by
      dsimp [K]
      rw [Real.div_rpow hc hlambda.le]
      have hpow : lambda ^ r ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hlambda r)
      field_simp

theorem superlevel_subset_strip_of_power_bound {E : Type*} [NormedAddCommGroup E]
    {p ell c : ℝ} (hp : 2 < p) (hc : 0 ≤ c) (F : Point → E)
    (haxis : ∀ z, z.2 = 0 → F z = 0)
    (hbound : ∀ z, z ∈ cube ell → z.2 ≠ 0 →
      ‖F z‖ ≤ c * |z.2| ^ (-singularityExponent p)) :
    ∀ lambda : ℝ, 0 < lambda →
      superlevelOn (cube ell) F lambda ⊆
        centralStrip ell ((c / lambda) ^ weakExponent p) := by
  intro lambda hlambda z hz
  rcases hz with ⟨hzCube, hlarge⟩
  by_cases hy0 : z.2 = 0
  · have hF0 : F z = 0 := haxis z hy0
    rw [hF0] at hlarge
    rw [norm_zero] at hlarge
    linarith
  have hypos : 0 < |z.2| := abs_pos.mpr hy0
  have ha : 0 < singularityExponent p := (singularityExponent_mem_Ioo hp).1
  have hsingular : lambda < c * |z.2| ^ (-singularityExponent p) :=
    lt_of_lt_of_le hlarge (hbound z hzCube hy0)
  have hdiv : lambda < c / |z.2| ^ singularityExponent p := by
    simpa [div_eq_mul_inv, Real.rpow_neg (abs_nonneg z.2)] using hsingular
  have hmul : lambda * |z.2| ^ singularityExponent p < c :=
    (lt_div_iff₀ (Real.rpow_pos_of_pos hypos _)).mp hdiv
  have hpower : |z.2| ^ singularityExponent p < c / lambda := by
    apply (lt_div_iff₀ hlambda).2
    simpa [mul_comm] using hmul
  have hwidth : |z.2| < (c / lambda) ^ (singularityExponent p)⁻¹ :=
    (Real.lt_rpow_inv_iff_of_pos (abs_nonneg z.2) (div_nonneg hc hlambda.le) ha).2 hpower
  refine ⟨hzCube.1, ?_⟩
  have hwidth' : |z.2| < (c / lambda) ^ weakExponent p := by
    simpa [weakExponent_eq_inv_singularity hp] using hwidth
  exact abs_lt.mp hwidth'

theorem stress_has_weak_p_over_two_tail {E : Type*} [Norm E]
    {p ell c : ℝ} (hp : 2 < p) (hell : 0 ≤ ell) (hc : 0 ≤ c) (F : Point → E)
    (hsubset : ∀ lambda : ℝ, 0 < lambda →
      superlevelOn (cube ell) F lambda ⊆
        centralStrip ell ((c / lambda) ^ weakExponent p)) :
    HasWeakLpTailOn volume (weakExponent p) (cube ell) F := by
  apply weakTail_of_superlevel_subset_strip hell hc
  · rw [weakExponent]
    positivity
  · exact hsubset

theorem stress_has_weak_p_over_two_tail_of_power_bound {E : Type*} [NormedAddCommGroup E]
    {p ell c : ℝ} (hp : 2 < p) (hell : 0 ≤ ell) (hc : 0 ≤ c) (F : Point → E)
    (haxis : ∀ z, z.2 = 0 → F z = 0)
    (hbound : ∀ z, z ∈ cube ell → z.2 ≠ 0 →
      ‖F z‖ ≤ c * |z.2| ^ (-singularityExponent p)) :
    HasWeakLpTailOn volume (weakExponent p) (cube ell) F := by
  apply stress_has_weak_p_over_two_tail hp hell hc F
  exact superlevel_subset_strip_of_power_bound hp hc F haxis hbound

/-! ## Decay of the normal stress and removal of the interface -/

/-- Uniform convergence to zero on a family indexed by `xs`. -/
def UniformlyVanishesOn (xs : Set ℝ) (F2 : ℝ → ℝ → ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∀ᶠ y in 𝓝 0, ∀ x, x ∈ xs → |F2 x y| < epsilon

theorem normalStress_uniformly_vanishes {p c : ℝ} (hp : 2 < p) (_hc : 0 ≤ c)
    {xs : Set ℝ} {F2 : ℝ → ℝ → ℝ}
    (hbound : ∀ x, x ∈ xs → ∀ y,
      |F2 x y| ≤ c * |y| ^ decayExponent p) :
    UniformlyVanishesOn xs F2 := by
  have habs : Tendsto (fun y : ℝ => |y|) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs : Continuous (abs : ℝ → ℝ)).tendsto 0
  have hpower : Tendsto (fun y : ℝ => |y| ^ decayExponent p) (𝓝 0) (𝓝 0) :=
    habs.rpow_const_nhds_zero (decayExponent_pos hp)
  have hmajor : Tendsto (fun y : ℝ => c * |y| ^ decayExponent p) (𝓝 0) (𝓝 0) :=
    by simpa using (tendsto_const_nhds (x := c)).mul hpower
  intro epsilon hepsilon
  have heventually : ∀ᶠ y in 𝓝 0, c * |y| ^ decayExponent p < epsilon :=
    (tendsto_order.1 hmajor).2 epsilon hepsilon
  filter_upwards [heventually] with y hy
  intro x hx
  exact lt_of_le_of_lt (hbound x hx y) hy

theorem centralStrip_setIntegral_tendsto_zero {ell : ℝ} (hell : 0 ≤ ell)
    {f : Point → ℝ} (hf : Integrable f) :
    Tendsto (fun delta : ℝ => ∫ z in centralStrip ell delta, f z)
      (𝓝[>] 0) (𝓝 0) := by
  apply hf.tendsto_setIntegral_nhds_zero
  simpa [Function.comp_def] using centralStrip_volume_tendsto_zero hell

/--
The removable-interface step.  Here `outer delta` is the integral on the two excised
rectangles after integration by parts, and `f` is `<stress, D phi>`.  The hypotheses
`hsplit` and `houter` are exactly what off-axis divergence-freeness and the normal-stress
bound provide in (3.27); integrability and shrinking-strip volume dispose of (II).
-/
theorem weakEuler_of_excision {p ell C weakIntegral : ℝ}
    (hp : 2 < p) (hell : 0 ≤ ell) (_hC : 0 ≤ C)
    (f : Point → ℝ) (hf : Integrable f) (outer : ℝ → ℝ)
    (hsplit : (fun _ : ℝ => weakIntegral) =ᶠ[𝓝[>] 0]
      fun delta => outer delta + ∫ z in centralStrip ell delta, f z)
    (houter : ∀ᶠ delta in 𝓝[>] 0,
      |outer delta| ≤ C * delta ^ decayExponent p) :
    weakIntegral = 0 := by
  have hid : Tendsto (fun delta : ℝ => delta) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hpower : Tendsto (fun delta : ℝ => delta ^ decayExponent p)
      (𝓝[>] 0) (𝓝 0) :=
    hid.rpow_const_nhds_zero (decayExponent_pos hp)
  have hmajor : Tendsto (fun delta : ℝ => C * delta ^ decayExponent p)
      (𝓝[>] 0) (𝓝 0) :=
    by simpa using (tendsto_const_nhds (x := C)).mul hpower
  have habsOuter : Tendsto (fun delta : ℝ => |outer delta|)
      (𝓝[>] 0) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) houter hmajor
  have houterZero : Tendsto outer (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    simpa [Function.comp_def] using habsOuter
  have hstripZero := centralStrip_setIntegral_tendsto_zero hell hf
  have hsum : Tendsto
      (fun delta => outer delta + ∫ z in centralStrip ell delta, f z)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using houterZero.add hstripZero
  have hconst : Tendsto (fun _ : ℝ => weakIntegral) (𝓝[>] 0) (𝓝 0) :=
    hsum.congr' hsplit.symm
  exact tendsto_nhds_unique tendsto_const_nhds hconst

/-! ## Convex variational conclusion -/

section Variational

variable {Omega E : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The closed unit ball, the pointwise domain of the Born--Infeld density. -/
def closedUnitBall : Set E := {z | ‖z‖ ≤ 1}

/-- The algebraic finite branch of the Born--Infeld density. -/
def bornInfeldFiniteBranch (q : ℝ) (z : E) : ℝ :=
  (1 - ‖z‖ ^ q) ^ q⁻¹

/--
A real-valued representative of the Born--Infeld density: its finite branch on
the closed unit ball and zero elsewhere.  All variational theorems below that
instantiate this density explicitly require admissible gradients to lie in the
closed unit ball a.e.; the value chosen outside is therefore immaterial.
-/
def bornInfeldDensity (q : ℝ) (z : E) : ℝ :=
  if ‖z‖ ≤ 1 then bornInfeldFiniteBranch q z else 0

/-- The real-valued finite representative of the convex density. -/
def tildeBornInfeldDensity (q : ℝ) (z : E) : ℝ :=
  -bornInfeldDensity q z

/-- The paper's extended convex density, with value `+∞` outside the unit ball. -/
def extendedTildeBornInfeldDensity (q : ℝ) (z : E) : EReal :=
  if ‖z‖ ≤ 1 then ((-bornInfeldFiniteBranch q z : ℝ) : EReal) else ⊤

omit [InnerProductSpace ℝ E] in
@[simp]
theorem bornInfeldDensity_of_norm_le {q : ℝ} {z : E} (hz : ‖z‖ ≤ 1) :
    bornInfeldDensity q z = bornInfeldFiniteBranch q z := by
  simp [bornInfeldDensity, hz]

omit [InnerProductSpace ℝ E] in
@[simp]
theorem extendedTildeBornInfeldDensity_of_norm_le {q : ℝ} {z : E}
    (hz : ‖z‖ ≤ 1) :
    extendedTildeBornInfeldDensity q z =
      ((-bornInfeldFiniteBranch q z : ℝ) : EReal) := by
  simp [extendedTildeBornInfeldDensity, hz]

omit [InnerProductSpace ℝ E] in
@[simp]
theorem extendedTildeBornInfeldDensity_of_one_lt_norm {q : ℝ} {z : E}
    (hz : 1 < ‖z‖) : extendedTildeBornInfeldDensity q z = ⊤ := by
  simp [extendedTildeBornInfeldDensity, not_le.mpr hz]

/-- Integral energy evaluated on a gradient field. -/
def Energy (mu : Measure Omega) (j : E → ℝ) (D : Omega → E) : ℝ :=
  ∫ x, j (D x) ∂mu

omit [InnerProductSpace ℝ E] in
theorem bornInfeld_energy_sign (mu : Measure Omega) (q : ℝ) (D : Omega → E) :
    Energy mu (bornInfeldDensity q) D =
      -Energy mu (tildeBornInfeldDensity q) D := by
  simp only [Energy, tildeBornInfeldDensity]
  rw [integral_neg]
  simp

/-- Supporting-hyperplane inequality at `z`, with subgradient `sigma`. -/
def IsSubgradientAt (j : E → ℝ) (z sigma : E) : Prop :=
  ∀ w, j z + inner ℝ sigma (w - z) ≤ j w

/-- Supporting-hyperplane inequality relative to a pointwise convex domain. -/
def IsSubgradientAtOn (domain : Set E) (j : E → ℝ) (z sigma : E) : Prop :=
  z ∈ domain ∧ ∀ w, w ∈ domain → j z + inner ℝ sigma (w - z) ≤ j w

/-- Maximality among admissible gradient fields. -/
def IsMaximizerOn (mu : Measure Omega) (j : E → ℝ)
    (admissible : Set (Omega → E)) (Du : Omega → E) : Prop :=
  Du ∈ admissible ∧ ∀ Dw, Dw ∈ admissible → Energy mu j Dw ≤ Energy mu j Du

/-- Maximality for maps after applying an abstract gradient operator. -/
def IsMapMaximizerOn {U : Type*} (mu : Measure Omega) (j : E → ℝ)
    (gradient : U → Omega → E) (admissible : Set U) (u : U) : Prop :=
  u ∈ admissible ∧ ∀ w, w ∈ admissible →
    Energy mu j (gradient w) ≤ Energy mu j (gradient u)

/-- The a.e. unit-gradient constraint in the admissible Born--Infeld class. -/
def HasUnitGradient (mu : Measure Omega) (D : Omega → E) : Prop :=
  ∀ᵐ x ∂mu, ‖D x‖ ≤ 1

theorem energy_le_of_subgradient_and_weakEuler {mu : Measure Omega} {j : E → ℝ}
    {Du Dw stress : Omega → E}
    (hju : Integrable (fun x => j (Du x)) mu)
    (hjw : Integrable (fun x => j (Dw x)) mu)
    (hlinear : Integrable (fun x => inner ℝ (stress x) (Dw x - Du x)) mu)
    (hsubgradient : ∀ᵐ x ∂mu, IsSubgradientAt j (Du x) (stress x))
    (hweakEuler : ∫ x, inner ℝ (stress x) (Dw x - Du x) ∂mu = 0) :
    Energy mu j Du ≤ Energy mu j Dw := by
  have hpointwise : ∀ᵐ x ∂mu,
      j (Du x) + inner ℝ (stress x) (Dw x - Du x) ≤ j (Dw x) := by
    filter_upwards [hsubgradient] with x hx
    exact hx (Dw x)
  calc
    Energy mu j Du = ∫ x, j (Du x) + inner ℝ (stress x) (Dw x - Du x) ∂mu := by
      rw [integral_add hju hlinear, hweakEuler, add_zero]
      rfl
    _ ≤ ∫ x, j (Dw x) ∂mu :=
      integral_mono_ae (hju.add hlinear) hjw hpointwise
    _ = Energy mu j Dw := rfl

/--
The same convexity argument for a density whose finite branch is considered
only on a pointwise domain (the closed unit ball in the Born--Infeld case).
-/
theorem energy_le_of_subgradientOn_and_weakEuler {mu : Measure Omega}
    {domain : Set E} {j : E → ℝ} {Du Dw stress : Omega → E}
    (hju : Integrable (fun x => j (Du x)) mu)
    (hjw : Integrable (fun x => j (Dw x)) mu)
    (hlinear : Integrable (fun x => inner ℝ (stress x) (Dw x - Du x)) mu)
    (hDwDomain : ∀ᵐ x ∂mu, Dw x ∈ domain)
    (hsubgradient : ∀ᵐ x ∂mu, IsSubgradientAtOn domain j (Du x) (stress x))
    (hweakEuler : ∫ x, inner ℝ (stress x) (Dw x - Du x) ∂mu = 0) :
    Energy mu j Du ≤ Energy mu j Dw := by
  have hpointwise : ∀ᵐ x ∂mu,
      j (Du x) + inner ℝ (stress x) (Dw x - Du x) ≤ j (Dw x) := by
    filter_upwards [hsubgradient, hDwDomain] with x hx hDw
    exact hx.2 (Dw x) hDw
  calc
    Energy mu j Du = ∫ x, j (Du x) + inner ℝ (stress x) (Dw x - Du x) ∂mu := by
      rw [integral_add hju hlinear, hweakEuler, add_zero]
      rfl
    _ ≤ ∫ x, j (Dw x) ∂mu :=
      integral_mono_ae (hju.add hlinear) hjw hpointwise
    _ = Energy mu j Dw := rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem negEnergy_reverses_inequality {mu : Measure Omega} {j : E → ℝ}
    {Du Dw : Omega → E} (h : Energy mu j Du ≤ Energy mu j Dw) :
    Energy mu (fun z => -j z) Dw ≤ Energy mu (fun z => -j z) Du := by
  simpa only [Energy, integral_neg] using neg_le_neg h

/--
The final maximality argument: the convex density `jTilde` is minimized, hence its negative
(the Born--Infeld density on the admissible unit-gradient class) is maximized.
-/
theorem weakEuler_implies_dirichlet_maximality {mu : Measure Omega} {jTilde : E → ℝ}
    {admissible : Set (Omega → E)} {Du stress : Omega → E}
    (hDu : Du ∈ admissible)
    (hju : Integrable (fun x => jTilde (Du x)) mu)
    (hsubgradient : ∀ᵐ x ∂mu, IsSubgradientAt jTilde (Du x) (stress x))
    (hcompetitor : ∀ Dw, Dw ∈ admissible →
      Integrable (fun x => jTilde (Dw x)) mu ∧
      Integrable (fun x => inner ℝ (stress x) (Dw x - Du x)) mu ∧
      (∫ x, inner ℝ (stress x) (Dw x - Du x) ∂mu) = 0) :
    IsMaximizerOn mu (fun z => -jTilde z) admissible Du := by
  refine ⟨hDu, fun Dw hDw => ?_⟩
  rcases hcompetitor Dw hDw with ⟨hjw, hlinear, hweakEuler⟩
  exact negEnergy_reverses_inequality <|
    energy_le_of_subgradient_and_weakEuler hju hjw hlinear hsubgradient hweakEuler

theorem weakEuler_implies_dirichlet_maximality_for_maps {U : Type*}
    {mu : Measure Omega} {jTilde : E → ℝ} {gradient : U → Omega → E}
    {admissible : Set U} {u : U} {stress : Omega → E}
    (hu : u ∈ admissible)
    (hju : Integrable (fun x => jTilde (gradient u x)) mu)
    (hsubgradient : ∀ᵐ x ∂mu,
      IsSubgradientAt jTilde (gradient u x) (stress x))
    (hcompetitor : ∀ w, w ∈ admissible →
      Integrable (fun x => jTilde (gradient w x)) mu ∧
      Integrable (fun x => inner ℝ (stress x) (gradient w x - gradient u x)) mu ∧
      (∫ x, inner ℝ (stress x) (gradient w x - gradient u x) ∂mu) = 0) :
    IsMapMaximizerOn mu (fun z => -jTilde z) gradient admissible u := by
  refine ⟨hu, fun w hw => ?_⟩
  rcases hcompetitor w hw with ⟨hjw, hlinear, hweakEuler⟩
  exact negEnergy_reverses_inequality <|
    energy_le_of_subgradient_and_weakEuler hju hjw hlinear hsubgradient hweakEuler

/--
Map-level maximality using a supporting inequality restricted to a pointwise
domain.  Every admissible competitor is required to have gradient in that
domain almost everywhere.
-/
theorem weakEuler_implies_dirichlet_maximality_for_maps_on {U : Type*}
    {mu : Measure Omega} {domain : Set E} {jTilde : E → ℝ}
    {gradient : U → Omega → E} {admissible : Set U} {u : U}
    {stress : Omega → E}
    (hu : u ∈ admissible)
    (hgradientDomain : ∀ w, w ∈ admissible →
      ∀ᵐ x ∂mu, gradient w x ∈ domain)
    (hju : Integrable (fun x => jTilde (gradient u x)) mu)
    (hsubgradient : ∀ᵐ x ∂mu,
      IsSubgradientAtOn domain jTilde (gradient u x) (stress x))
    (hcompetitor : ∀ w, w ∈ admissible →
      Integrable (fun x => jTilde (gradient w x)) mu ∧
      Integrable (fun x => inner ℝ (stress x) (gradient w x - gradient u x)) mu ∧
      (∫ x, inner ℝ (stress x) (gradient w x - gradient u x) ∂mu) = 0) :
    IsMapMaximizerOn mu (fun z => -jTilde z) gradient admissible u := by
  refine ⟨hu, fun w hw => ?_⟩
  rcases hcompetitor w hw with ⟨hjw, hlinear, hweakEuler⟩
  exact negEnergy_reverses_inequality <|
    energy_le_of_subgradientOn_and_weakEuler hju hjw hlinear
      (hgradientDomain w hw) hsubgradient hweakEuler

/--
Born--Infeld specialization on the a.e. unit-gradient Dirichlet class.  This
uses only the finite branch; `extendedTildeBornInfeldDensity` records the
corresponding `+∞` extension from the paper.
-/
theorem weakEuler_implies_bornInfeld_maximality_for_maps {U : Type*}
    {mu : Measure Omega} (q : ℝ) {gradient : U → Omega → E}
    {admissible : Set U} {u : U} {stress : Omega → E}
    (hu : u ∈ admissible)
    (hunit : ∀ w, w ∈ admissible → HasUnitGradient mu (gradient w))
    (hju : Integrable
      (fun x => tildeBornInfeldDensity q (gradient u x)) mu)
    (hsubgradient : ∀ᵐ x ∂mu,
      IsSubgradientAtOn (closedUnitBall : Set E)
        (tildeBornInfeldDensity q) (gradient u x) (stress x))
    (hcompetitor : ∀ w, w ∈ admissible →
      Integrable (fun x => tildeBornInfeldDensity q (gradient w x)) mu ∧
      Integrable (fun x => inner ℝ (stress x) (gradient w x - gradient u x)) mu ∧
      (∫ x, inner ℝ (stress x) (gradient w x - gradient u x) ∂mu) = 0) :
    IsMapMaximizerOn mu (bornInfeldDensity q) gradient admissible u := by
  have hdomain : ∀ w, w ∈ admissible →
      ∀ᵐ x ∂mu, gradient w x ∈ (closedUnitBall : Set E) := by
    intro w hw
    simpa only [HasUnitGradient, closedUnitBall, Set.mem_ofPred_eq] using hunit w hw
  simpa only [tildeBornInfeldDensity, neg_neg] using
    (weakEuler_implies_dirichlet_maximality_for_maps_on
      (domain := (closedUnitBall : Set E)) hu hdomain hju hsubgradient hcompetitor)

end Variational

section Combined

variable {U E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
Paper-facing combination of the removable-interface and convexity arguments.  Gradient fields are
extended to all of `R^2`; the energy measure is restricted to the cube.  The globally integrable
first-variation integrand is the convenient zero extension used for strip excision.
-/
theorem maximality_of_u_from_excision {p ell C : ℝ}
    (hp : 2 < p) (hell : 0 < ell) (hC : 0 ≤ C)
    {jTilde : E → ℝ} {gradient : U → Point → E} {admissible : Set U}
    {u : U} {stress : Point → E}
    (hu : u ∈ admissible)
    (hju : Integrable (fun z => jTilde (gradient u z)) (volume.restrict (cube ell)))
    (hsubgradient : ∀ᵐ z ∂(volume.restrict (cube ell)),
      IsSubgradientAt jTilde (gradient u z) (stress z))
    (hcompetitor : ∀ w, w ∈ admissible →
      Integrable (fun z => jTilde (gradient w z)) (volume.restrict (cube ell)) ∧
      IntegrableOn (fun z => inner ℝ (stress z) (gradient w z - gradient u z))
        (cube ell) volume ∧
      ∃ outer : ℝ → ℝ,
        ((fun _ : ℝ => ∫ z in cube ell,
            inner ℝ (stress z) (gradient w z - gradient u z)) =ᶠ[𝓝[>] 0]
          fun delta => outer delta +
            ∫ z in centralStrip ell delta,
              (cube ell).indicator
                (fun z => inner ℝ (stress z) (gradient w z - gradient u z)) z) ∧
        (∀ᶠ delta in 𝓝[>] 0, |outer delta| ≤ C * delta ^ decayExponent p)) :
    IsMapMaximizerOn (volume.restrict (cube ell)) (fun z => -jTilde z)
      gradient admissible u := by
  apply weakEuler_implies_dirichlet_maximality_for_maps hu hju hsubgradient
  intro w hw
  rcases hcompetitor w hw with ⟨hjw, hlinear, outer, hsplit, houter⟩
  refine ⟨hjw, hlinear, ?_⟩
  change (∫ z in cube ell,
    inner ℝ (stress z) (gradient w z - gradient u z)) = 0
  exact weakEuler_of_excision hp hell.le hC _
    (hlinear.integrable_indicator (cube_measurable ell)) outer hsplit houter

/--
Born--Infeld specialization of the excision argument.  Unlike the abstract
theorem above, this statement records the a.e. unit-gradient restriction and
uses the relative subgradient inequality on the closed unit ball.
-/
theorem bornInfeld_maximality_of_u_from_excision {p ell C q : ℝ}
    (hp : 2 < p) (hell : 0 < ell) (hC : 0 ≤ C)
    {gradient : U → Point → E} {admissible : Set U} {u : U}
    {stress : Point → E}
    (hu : u ∈ admissible)
    (hunit : ∀ w, w ∈ admissible →
      HasUnitGradient (volume.restrict (cube ell)) (gradient w))
    (hju : Integrable
      (fun z => tildeBornInfeldDensity q (gradient u z))
      (volume.restrict (cube ell)))
    (hsubgradient : ∀ᵐ z ∂(volume.restrict (cube ell)),
      IsSubgradientAtOn (closedUnitBall : Set E)
        (tildeBornInfeldDensity q) (gradient u z) (stress z))
    (hcompetitor : ∀ w, w ∈ admissible →
      Integrable (fun z => tildeBornInfeldDensity q (gradient w z))
        (volume.restrict (cube ell)) ∧
      IntegrableOn (fun z => inner ℝ (stress z) (gradient w z - gradient u z))
        (cube ell) volume ∧
      ∃ outer : ℝ → ℝ,
        ((fun _ : ℝ => ∫ z in cube ell,
            inner ℝ (stress z) (gradient w z - gradient u z)) =ᶠ[𝓝[>] 0]
          fun delta => outer delta +
            ∫ z in centralStrip ell delta,
              (cube ell).indicator
                (fun z => inner ℝ (stress z) (gradient w z - gradient u z)) z) ∧
        (∀ᶠ delta in 𝓝[>] 0, |outer delta| ≤ C * delta ^ decayExponent p)) :
    IsMapMaximizerOn (volume.restrict (cube ell)) (bornInfeldDensity q)
      gradient admissible u := by
  apply weakEuler_implies_bornInfeld_maximality_for_maps q hu hunit hju hsubgradient
  intro w hw
  rcases hcompetitor w hw with ⟨hjw, hlinear, outer, hsplit, houter⟩
  refine ⟨hjw, hlinear, ?_⟩
  change (∫ z in cube ell,
    inner ℝ (stress z) (gradient w z - gradient u z)) = 0
  exact weakEuler_of_excision hp hell.le hC _
    (hlinear.integrable_indicator (cube_measurable ell)) outer hsplit houter

end Combined

end MaximalityOfU
