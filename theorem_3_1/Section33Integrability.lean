import MaximalityOfU

/-!
# Integrability lemmas for the Section 3.3 maximality argument

This file discharges the routine, but logically necessary, measurability and
integrability hypotheses in the final convex-variational step.  The results
are stated for an arbitrary finite-measure localization before being
specialized to the manuscript cube.
-/

open MeasureTheory Set

noncomputable section

namespace Section33Integrability

/-! ## The finite Born--Infeld density -/

section Density

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]

/-- The finite Born--Infeld branch is a Borel function for positive `q`. -/
theorem bornInfeldFiniteBranch_measurable
    {q : ℝ} (hq : 0 < q) :
    Measurable (MaximalityOfU.bornInfeldFiniteBranch q : E → ℝ) := by
  have hnorm : Measurable (fun z : E => ‖z‖) := continuous_norm.measurable
  have hpow : Measurable (fun z : E => ‖z‖ ^ q) :=
    (Real.continuous_rpow_const hq.le).measurable.comp hnorm
  have hbase : Measurable (fun z : E => 1 - ‖z‖ ^ q) :=
    measurable_const.sub hpow
  have hroot : Measurable (fun z : E => (1 - ‖z‖ ^ q) ^ q⁻¹) :=
    (Real.continuous_rpow_const (inv_nonneg.mpr hq.le)).measurable.comp hbase
  change Measurable (fun z : E => (1 - ‖z‖ ^ q) ^ q⁻¹)
  exact hroot

/-- The total real-valued representative of the Born--Infeld density is
Borel measurable. -/
theorem bornInfeldDensity_measurable
    {q : ℝ} (hq : 0 < q) :
    Measurable (MaximalityOfU.bornInfeldDensity q : E → ℝ) := by
  have hball : MeasurableSet {z : E | ‖z‖ ≤ 1} :=
    measurableSet_le continuous_norm.measurable measurable_const
  change Measurable (fun z : E => if ‖z‖ ≤ 1 then
    MaximalityOfU.bornInfeldFiniteBranch q z else 0)
  exact Measurable.ite hball
    (bornInfeldFiniteBranch_measurable (E := E) hq) measurable_const

/-- The convex density `-J_q` used in the maximality proof is Borel
measurable. -/
theorem tildeBornInfeldDensity_measurable
    {q : ℝ} (hq : 0 < q) :
    Measurable (MaximalityOfU.tildeBornInfeldDensity q : E → ℝ) := by
  change Measurable (fun z : E => -MaximalityOfU.bornInfeldDensity q z)
  exact (bornInfeldDensity_measurable (E := E) hq).neg

omit [MeasurableSpace E] [BorelSpace E] in
/-- On the closed unit ball, the absolute value of the finite convex density
is bounded by one. -/
theorem norm_tildeBornInfeldDensity_le_one
    {q : ℝ} (hq : 0 < q) {z : E} (hz : ‖z‖ ≤ 1) :
    ‖MaximalityOfU.tildeBornInfeldDensity q z‖ ≤ 1 := by
  have hpow0 : 0 ≤ ‖z‖ ^ q := Real.rpow_nonneg (norm_nonneg z) q
  have hpow1 : ‖z‖ ^ q ≤ 1 :=
    Real.rpow_le_one (norm_nonneg z) hz hq.le
  have hbase0 : 0 ≤ 1 - ‖z‖ ^ q := sub_nonneg.mpr hpow1
  have hbase1 : 1 - ‖z‖ ^ q ≤ 1 := by linarith
  have hroot0 : 0 ≤ (1 - ‖z‖ ^ q) ^ q⁻¹ :=
    Real.rpow_nonneg hbase0 q⁻¹
  have hroot1 : (1 - ‖z‖ ^ q) ^ q⁻¹ ≤ 1 :=
    Real.rpow_le_one hbase0 hbase1 (inv_nonneg.mpr hq.le)
  rw [MaximalityOfU.tildeBornInfeldDensity,
    MaximalityOfU.bornInfeldDensity_of_norm_le hz,
    MaximalityOfU.bornInfeldFiniteBranch, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg hroot0]
  exact hroot1

end Density

section Composition

variable {Omega E : Type*} [MeasurableSpace Omega]
  [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]

/-- Composing the Borel Born--Infeld density with an a.e. strongly measurable
field preserves a.e. strong measurability. -/
theorem tildeBornInfeldDensity_comp_aestronglyMeasurable
    {mu : Measure Omega} {q : ℝ} (hq : 0 < q) {D : Omega → E}
    (hD : AEStronglyMeasurable D mu) :
    AEStronglyMeasurable
      (fun x => MaximalityOfU.tildeBornInfeldDensity q (D x)) mu := by
  have hcomp : AEMeasurable
      (MaximalityOfU.tildeBornInfeldDensity q ∘ D) mu :=
    (tildeBornInfeldDensity_measurable (E := E) hq).comp_aemeasurable
      hD.aemeasurable
  change AEStronglyMeasurable
    (MaximalityOfU.tildeBornInfeldDensity q ∘ D) mu
  exact hcomp.aestronglyMeasurable

/-- On a finite-measure localization, every a.e. strongly measurable
unit-bounded field has integrable finite Born--Infeld density. -/
theorem tildeBornInfeldDensity_integrableOn_of_unit_bound
    {mu : Measure Omega} {s : Set Omega} (hsfinite : mu s ≠ ⊤)
    {q : ℝ} (hq : 0 < q) {D : Omega → E}
    (hD : AEStronglyMeasurable D (mu.restrict s))
    (hunit : ∀ᵐ x ∂(mu.restrict s), ‖D x‖ ≤ 1) :
    IntegrableOn
      (fun x => MaximalityOfU.tildeBornInfeldDensity q (D x)) s mu := by
  have hone : IntegrableOn (fun _ : Omega => (1 : ℝ)) s mu :=
    integrableOn_const hsfinite
  refine hone.mono'
    (tildeBornInfeldDensity_comp_aestronglyMeasurable hq hD) ?_
  filter_upwards [hunit] with x hx
  exact norm_tildeBornInfeldDensity_le_one hq hx

/-- Cube-specialized version of
`tildeBornInfeldDensity_integrableOn_of_unit_bound`. -/
theorem tildeBornInfeldDensity_integrableOn_cube
    {q ell : ℝ} (hq : 0 < q) {D : MaximalityOfU.Point → E}
    (hD : AEStronglyMeasurable D
      (volume.restrict (MaximalityOfU.cube ell)))
    (hunit : ∀ᵐ z ∂(volume.restrict (MaximalityOfU.cube ell)),
      ‖D z‖ ≤ 1) :
    IntegrableOn
      (fun z => MaximalityOfU.tildeBornInfeldDensity q (D z))
      (MaximalityOfU.cube ell) volume := by
  have hfinite : volume (MaximalityOfU.cube ell) ≠ ⊤ := by
    rw [MaximalityOfU.cube, Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_Ioo]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  exact tildeBornInfeldDensity_integrableOn_of_unit_bound
    hfinite hq hD hunit

end Composition

/-! ## Pairing an integrable stress with bounded gradients -/

section StressPairing

variable {Omega E : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An integrable stress paired with the difference of two measurable,
unit-bounded fields is integrable. -/
theorem inner_stress_sub_integrableOn_of_unit_bounds
    {mu : Measure Omega} {s : Set Omega}
    {stress Dw Du : Omega → E}
    (hstress : IntegrableOn stress s mu)
    (hDw : AEStronglyMeasurable Dw (mu.restrict s))
    (hDu : AEStronglyMeasurable Du (mu.restrict s))
    (hDwUnit : ∀ᵐ x ∂(mu.restrict s), ‖Dw x‖ ≤ 1)
    (hDuUnit : ∀ᵐ x ∂(mu.restrict s), ‖Du x‖ ≤ 1) :
    IntegrableOn (fun x => inner ℝ (stress x) (Dw x - Du x)) s mu := by
  have hmajor : IntegrableOn (fun x => 2 * ‖stress x‖) s mu :=
    hstress.norm.const_mul 2
  have hinnerMeas : AEStronglyMeasurable
      (fun x => inner ℝ (stress x) (Dw x - Du x)) (mu.restrict s) :=
    hstress.aestronglyMeasurable.inner (hDw.sub hDu)
  refine hmajor.mono' hinnerMeas ?_
  filter_upwards [hDwUnit, hDuUnit] with x hWx hUx
  calc
    ‖inner ℝ (stress x) (Dw x - Du x)‖ ≤
        ‖stress x‖ * ‖Dw x - Du x‖ := norm_inner_le_norm _ _
    _ ≤ ‖stress x‖ * (‖Dw x‖ + ‖Du x‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ ‖stress x‖ * 2 := by
      exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ = 2 * ‖stress x‖ := by ring

/-- Cube-specialized spelling of
`inner_stress_sub_integrableOn_of_unit_bounds`. -/
theorem inner_stress_sub_integrableOn_cube_of_unit_bounds
    {ell : ℝ}
    {stress Dw Du : MaximalityOfU.Point → E}
    (hstress : IntegrableOn stress (MaximalityOfU.cube ell) volume)
    (hDw : AEStronglyMeasurable Dw
      (volume.restrict (MaximalityOfU.cube ell)))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (MaximalityOfU.cube ell)))
    (hDwUnit : ∀ᵐ z ∂(volume.restrict (MaximalityOfU.cube ell)),
      ‖Dw z‖ ≤ 1)
    (hDuUnit : ∀ᵐ z ∂(volume.restrict (MaximalityOfU.cube ell)),
      ‖Du z‖ ≤ 1) :
    IntegrableOn
      (fun z => inner ℝ (stress z) (Dw z - Du z))
      (MaximalityOfU.cube ell) volume :=
  inner_stress_sub_integrableOn_of_unit_bounds
    hstress hDw hDu hDwUnit hDuUnit

end StressPairing

end Section33Integrability
