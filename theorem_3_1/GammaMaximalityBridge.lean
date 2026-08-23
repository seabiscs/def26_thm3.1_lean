import StressTensor
import MaximalityOfU

/-!
# Bridge from the earlier gamma construction to the maximality argument

This file proves that the ansatz, exponent, and factored stress used in the
two developments are literally the same objects.  It then gives concrete
specializations of the integrability, weak-tail, off-axis divergence, and
Born--Infeld maximality lemmas to a supplied `StressTensor.CKOutcome`.

`CKOutcome` is the explicit boundary of the earlier development: Mathlib does
not currently provide the Cauchy--Kowalevskaya theorem needed to construct one.
The uniform component estimates, integration-by-parts split, and relative
subgradient inequality also remain visible hypotheses below.
-/

open Filter MeasureTheory Set Topology

noncomputable section

namespace GammaMaximalityBridge

/-- The earlier curried ansatz viewed as a map on the plane. -/
def ansatzMap (gamma : ℝ → ℝ → ℝ) : MaximalityOfU.Point → ℝ :=
  fun z => StressTensor.ansatz gamma z.1 z.2

/-- The gradient field recorded by the actual `deriv`-jet of `gamma`. -/
def ansatzGradientField (gamma : ℝ → ℝ → ℝ) :
    MaximalityOfU.Point → MaximalityOfU.Vector2 :=
  fun z => (EuclideanSpace.equiv (Fin 2) ℝ).symm
    ![StressTensor.gamma1Field gamma z.1 z.2,
      2 * z.2 * StressTensor.gamma2Field gamma z.1 z.2]

/-- The total a.e. representative of the singular stress, set to zero on `y = 0`. -/
def stressField (P : StressTensor.Params) (gamma : ℝ → ℝ → ℝ) :
    MaximalityOfU.Point → MaximalityOfU.Vector2 :=
  MaximalityOfU.stressRepresentative P.p
    (fun z => StressTensor.scalarField P gamma z.1 z.2)
    (fun z => StressTensor.gamma1Field gamma z.1 z.2)
    (fun z => StressTensor.gamma2Field gamma z.1 z.2)

/-- The normal component of the total stress representative. -/
def normalStress (P : StressTensor.Params) (gamma : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  (EuclideanSpace.equiv (Fin 2) ℝ) (stressField P gamma (x, y)) 1

/-! ## Definitional compatibility -/

theorem ansatz_eq (gamma : ℝ → ℝ → ℝ) (x y : ℝ) :
    MaximalityOfU.ansatz (StressTensor.uncurried gamma) (x, y) =
      StressTensor.ansatz gamma x y := by
  rfl

theorem Gamma1_eq (gamma : ℝ → ℝ → ℝ) (x y : ℝ) :
    MaximalityOfU.Gamma1
        (fun z => StressTensor.partialX gamma z.1 z.2) (x, y) =
      StressTensor.gamma1 y (StressTensor.jetOf gamma x y) := by
  rfl

theorem Gamma2_eq (gamma : ℝ → ℝ → ℝ) (x y : ℝ) :
    MaximalityOfU.Gamma2 (StressTensor.uncurried gamma)
        (fun z => StressTensor.partialY gamma z.1 z.2) (x, y) =
      StressTensor.gamma2 y (StressTensor.jetOf gamma x y) := by
  rfl

theorem Gamma0_eq (gamma : ℝ → ℝ → ℝ) (x y : ℝ) :
    MaximalityOfU.Gamma0 (StressTensor.uncurried gamma)
        (fun z => StressTensor.partialX gamma z.1 z.2)
        (fun z => StressTensor.partialY gamma z.1 z.2) (x, y) =
      StressTensor.gamma0 y (StressTensor.jetOf gamma x y) := by
  rfl

/-- The exponent stored in the earlier parameter structure is `q / (q - 1)`. -/
theorem Params.p_eq_conjugateExponent (P : StressTensor.Params) :
    P.p = MaximalityOfU.conjugateExponent P.q := by
  have hp0 : P.p ≠ 0 := ne_of_gt P.p_pos
  have hq0 : P.q ≠ 0 := ne_of_gt P.q_pos
  have hqm1 : P.q - 1 ≠ 0 := ne_of_gt (sub_pos.mpr P.one_lt_q)
  have hh := P.holder
  rw [MaximalityOfU.conjugateExponent]
  field_simp [hp0, hq0, hqm1] at hh ⊢
  nlinarith

@[simp]
theorem ansatzMap_on_axis (gamma : ℝ → ℝ → ℝ) (x : ℝ) :
    ansatzMap gamma (x, 0) = x := by
  simp [ansatzMap, StressTensor.ansatz]

@[simp]
theorem stressField_on_axis (P : StressTensor.Params)
    (gamma : ℝ → ℝ → ℝ) (x : ℝ) :
    stressField P gamma (x, 0) = 0 := by
  simp [stressField]

@[simp]
theorem normalStress_on_axis (P : StressTensor.Params)
    (gamma : ℝ → ℝ → ℝ) (x : ℝ) :
    normalStress P gamma x 0 = 0 := by
  simp [normalStress]

theorem stressField_coord_zero_off_axis (P : StressTensor.Params)
    (gamma : ℝ → ℝ → ℝ) (x y : ℝ) (hy : y ≠ 0) :
    (EuclideanSpace.equiv (Fin 2) ℝ) (stressField P gamma (x, y)) 0 =
      StressTensor.singularStressX P gamma x y := by
  simp [stressField, MaximalityOfU.stressRepresentative, hy,
    StressTensor.singularStressX, StressTensor.singularDenominator,
    Real.rpow_eq_pow, Real.rpow_neg (abs_nonneg y), div_eq_mul_inv,
    mul_assoc, mul_comm]

theorem stressField_coord_one_off_axis (P : StressTensor.Params)
    (gamma : ℝ → ℝ → ℝ) (x y : ℝ) (hy : y ≠ 0) :
    (EuclideanSpace.equiv (Fin 2) ℝ) (stressField P gamma (x, y)) 1 =
      StressTensor.singularStressY P gamma x y := by
  simp [stressField, MaximalityOfU.stressRepresentative, hy,
    StressTensor.singularStressY, StressTensor.singularDenominator,
    Real.rpow_eq_pow, Real.rpow_neg (abs_nonneg y), div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm]

/-- The first component estimate in (3.27) from a uniform bound on `S * Gamma₁`. -/
theorem abs_stressField_coord_zero_le
    (P : StressTensor.Params) (gamma : ℝ → ℝ → ℝ) {x y A : ℝ}
    (hy : y ≠ 0)
    (hfactor : |StressTensor.scalarField P gamma x y *
      StressTensor.gamma1Field gamma x y| ≤ A) :
    |(EuclideanSpace.equiv (Fin 2) ℝ) (stressField P gamma (x, y)) 0| ≤
      A * |y| ^ (-MaximalityOfU.singularityExponent P.p) := by
  rw [stressField_coord_zero_off_axis P gamma x y hy]
  rw [StressTensor.singularStressX, StressTensor.singularDenominator,
    div_eq_mul_inv]
  have hinv : (Real.rpow |y| (2 / P.p))⁻¹ =
      Real.rpow |y| (-(2 / P.p)) := by
    simpa only [Real.rpow_eq_pow] using
      (Real.rpow_neg (abs_nonneg y) (2 / P.p)).symm
  rw [hinv]
  simp only [MaximalityOfU.singularityExponent, Real.rpow_eq_pow]
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) _)]
  exact mul_le_mul_of_nonneg_right hfactor
    (Real.rpow_nonneg (abs_nonneg y) _)

/-- The second component estimate in (3.27) from a uniform bound on `S * Gamma₂`. -/
theorem abs_normalStress_le
    (P : StressTensor.Params) (gamma : ℝ → ℝ → ℝ) {x y A : ℝ}
    (hy : y ≠ 0)
    (hfactor : |StressTensor.scalarField P gamma x y *
      StressTensor.gamma2Field gamma x y| ≤ A) :
    |normalStress P gamma x y| ≤
      2 * A * |y| ^ MaximalityOfU.decayExponent P.p := by
  have hypos : 0 < |y| := abs_pos.mpr hy
  have hdenom : 0 < Real.rpow |y| (2 / P.p) :=
    Real.rpow_pos_of_pos hypos _
  rw [normalStress, stressField_coord_one_off_axis P gamma x y hy]
  have habs :
      |StressTensor.singularStressY P gamma x y| =
        2 * |StressTensor.scalarField P gamma x y *
          StressTensor.gamma2Field gamma x y| *
          (|y| / Real.rpow |y| (2 / P.p)) := by
    simp only [StressTensor.singularStressY,
      StressTensor.singularDenominator, abs_mul, abs_div,
      abs_of_nonneg hdenom.le]
    norm_num
    ring
  rw [habs]
  calc
    2 * |StressTensor.scalarField P gamma x y *
          StressTensor.gamma2Field gamma x y| *
          (|y| / Real.rpow |y| (2 / P.p)) ≤
        2 * A * (|y| / Real.rpow |y| (2 / P.p)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfactor (by norm_num)) (by positivity)
    _ = 2 * A * |y| ^ MaximalityOfU.decayExponent P.p := by
      have hratio : |y| / Real.rpow |y| (2 / P.p) =
          Real.rpow |y| (1 - 2 / P.p) := by
        simpa only [Real.rpow_eq_pow, Real.rpow_one] using
          (Real.rpow_sub hypos 1 (2 / P.p)).symm
      rw [hratio, MaximalityOfU.decayExponent]
      rfl

/-! ## Section 3.3 estimates for the actual factored stress -/

theorem stressField_integrableOn_cube_of_power_bound
    (P : StressTensor.Params) (gamma : ℝ → ℝ → ℝ) {ell c : ℝ}
    (hell : 0 < ell)
    (hmeas : AEStronglyMeasurable (stressField P gamma)
      (volume.restrict (MaximalityOfU.cube ell)))
    (hbound : ∀ᵐ z ∂(volume.restrict (MaximalityOfU.cube ell)),
      ‖stressField P gamma z‖ ≤
        c * |z.2| ^ (-MaximalityOfU.singularityExponent P.p)) :
    IntegrableOn (stressField P gamma) (MaximalityOfU.cube ell) volume :=
  MaximalityOfU.stress_integrableOn_cube_of_power_bound
    P.two_lt_p hell hmeas hbound

theorem stressField_has_weak_p_over_two_tail_of_power_bound
    (P : StressTensor.Params) (gamma : ℝ → ℝ → ℝ) {ell c : ℝ}
    (hell : 0 ≤ ell) (hc : 0 ≤ c)
    (hbound : ∀ z, z ∈ MaximalityOfU.cube ell → z.2 ≠ 0 →
      ‖stressField P gamma z‖ ≤
        c * |z.2| ^ (-MaximalityOfU.singularityExponent P.p)) :
    MaximalityOfU.HasWeakLpTailOn volume
      (MaximalityOfU.weakExponent P.p) (MaximalityOfU.cube ell)
      (stressField P gamma) := by
  exact MaximalityOfU.stress_has_weak_p_over_two_tail_of_power_bound
    P.two_lt_p hell hc (stressField P gamma)
      (fun z hz => by rcases z with ⟨x, y⟩; simp_all) hbound

theorem normalStress_uniformly_vanishes
    (P : StressTensor.Params) (gamma : ℝ → ℝ → ℝ) {c : ℝ}
    (hc : 0 ≤ c) {xs : Set ℝ}
    (hbound : ∀ x, x ∈ xs → ∀ y,
      |normalStress P gamma x y| ≤
        c * |y| ^ MaximalityOfU.decayExponent P.p) :
    MaximalityOfU.UniformlyVanishesOn xs (normalStress P gamma) :=
  MaximalityOfU.normalStress_uniformly_vanishes P.two_lt_p hc hbound

theorem normalStress_uniformly_vanishes_of_factor_bound
    (P : StressTensor.Params) (gamma : ℝ → ℝ → ℝ) {A : ℝ}
    (hA : 0 ≤ A) {xs : Set ℝ}
    (hfactor : ∀ x, x ∈ xs → ∀ y, y ≠ 0 →
      |StressTensor.scalarField P gamma x y *
        StressTensor.gamma2Field gamma x y| ≤ A) :
    MaximalityOfU.UniformlyVanishesOn xs (normalStress P gamma) := by
  apply MaximalityOfU.normalStress_uniformly_vanishes (c := 2 * A) P.two_lt_p
    (mul_nonneg (by norm_num) hA)
  intro x hx y
  by_cases hy : y = 0
  · subst y
    rw [normalStress_on_axis]
    simp only [abs_zero]
    rw [Real.zero_rpow
      (ne_of_gt (MaximalityOfU.decayExponent_pos P.two_lt_p))]
    norm_num
  · exact abs_normalStress_le P gamma hy (hfactor x hx y hy)

/-! ## The earlier PDE implies off-axis divergence-freeness -/

theorem CKOutcome.singularStressDivergence_eq_zero
    {P : StressTensor.Params} {domain : Set StressTensor.Point} {r x y : ℝ}
    (K : StressTensor.CKOutcome P domain r) (hxy : (x, y) ∈ domain)
    (hy0 : y ≠ 0)
    (hx : HasDerivAt (fun xi => K.gamma xi y)
      (StressTensor.partialX K.gamma x y) x)
    (hxx : HasDerivAt (fun xi => StressTensor.partialX K.gamma xi y)
      (StressTensor.partialXX K.gamma x y) x)
    (hyx : HasDerivAt (fun xi => StressTensor.partialY K.gamma xi y)
      (StressTensor.partialXY K.gamma x y) x)
    (hy : HasDerivAt (K.gamma x) (StressTensor.partialY K.gamma x y) y)
    (hxyDeriv : HasDerivAt (fun eta => StressTensor.partialX K.gamma x eta)
      (StressTensor.partialXY K.gamma x y) y)
    (hyy : HasDerivAt (fun eta => StressTensor.partialY K.gamma x eta)
      (StressTensor.partialYY K.gamma x y) y)
    (hS : HasFDerivAt (StressTensor.stildeUncurried P)
      (StressTensor.scalarDifferential
        (StressTensor.scalarDataField P K.gamma x y))
      (y, StressTensor.gamma0Field K.gamma x y)) :
    StressTensor.singularStressDivergence P K.gamma x y = 0 := by
  rw [StressTensor.singularStressDivergence_eq_rpow_mul_residualNormal
    hy0 hx hxx hyx hy hxyDeriv hyy hS]
  have hres := K.solution.2.1 hxy
  have hres' :
      StressTensor.residualNormal P y (StressTensor.jetOf K.gamma x y)
        (StressTensor.partialXX K.gamma x y)
        (StressTensor.scalarDataField P K.gamma x y) = 0 := by
    simpa [StressTensor.auxiliaryEquationAt,
      StressTensor.scalarDataField] using hres
  rw [hres', mul_zero]

/-! ## Concrete Born--Infeld conclusion for a supplied CK outcome -/

/--
The paper-facing conditional endpoint.  The earlier `CKOutcome` supplies the
actual analytic `gamma`; the remaining hypotheses expose precisely the
Section 3.3 component estimates, excision/IBP boundary control, admissible
unit-gradient class, and relative subgradient inequality.
-/
theorem CKOutcome.ansatz_bornInfeld_maximality_from_excision
    {P : StressTensor.Params} {domain : Set StressTensor.Point} {r ell C : ℝ}
    (K : StressTensor.CKOutcome P domain r)
    (hell : 0 < ell) (hC : 0 ≤ C)
    {gradient : (MaximalityOfU.Point → ℝ) →
      MaximalityOfU.Point → MaximalityOfU.Vector2}
    {admissible : Set (MaximalityOfU.Point → ℝ)}
    (hu : ansatzMap K.gamma ∈ admissible)
    (hgradient : gradient (ansatzMap K.gamma) = ansatzGradientField K.gamma)
    (hunit : ∀ w, w ∈ admissible →
      MaximalityOfU.HasUnitGradient
        (volume.restrict (MaximalityOfU.cube ell)) (gradient w))
    (hju : Integrable
      (fun z => MaximalityOfU.tildeBornInfeldDensity P.q
        (ansatzGradientField K.gamma z))
      (volume.restrict (MaximalityOfU.cube ell)))
    (hsubgradient : ∀ᵐ z ∂(volume.restrict (MaximalityOfU.cube ell)),
      MaximalityOfU.IsSubgradientAtOn
        (MaximalityOfU.closedUnitBall : Set MaximalityOfU.Vector2)
        (MaximalityOfU.tildeBornInfeldDensity P.q)
        (ansatzGradientField K.gamma z) (stressField P K.gamma z))
    (hcompetitor : ∀ w, w ∈ admissible →
      Integrable (fun z => MaximalityOfU.tildeBornInfeldDensity P.q
        (gradient w z)) (volume.restrict (MaximalityOfU.cube ell)) ∧
      IntegrableOn (fun z => inner ℝ (stressField P K.gamma z)
        (gradient w z - ansatzGradientField K.gamma z))
        (MaximalityOfU.cube ell) volume ∧
      ∃ outer : ℝ → ℝ,
        ((fun _ : ℝ => ∫ z in MaximalityOfU.cube ell,
            inner ℝ (stressField P K.gamma z)
              (gradient w z - ansatzGradientField K.gamma z)) =ᶠ[𝓝[>] 0]
          fun delta => outer delta +
            ∫ z in MaximalityOfU.centralStrip ell delta,
              (MaximalityOfU.cube ell).indicator
                (fun z => inner ℝ (stressField P K.gamma z)
                  (gradient w z - ansatzGradientField K.gamma z)) z) ∧
        (∀ᶠ delta in 𝓝[>] 0,
          |outer delta| ≤ C * delta ^ MaximalityOfU.decayExponent P.p)) :
    MaximalityOfU.IsMapMaximizerOn
      (volume.restrict (MaximalityOfU.cube ell))
      (MaximalityOfU.bornInfeldDensity P.q) gradient admissible
      (ansatzMap K.gamma) := by
  apply MaximalityOfU.bornInfeld_maximality_of_u_from_excision
    P.two_lt_p hell hC hu hunit
  · simpa only [hgradient] using hju
  · simpa only [hgradient] using hsubgradient
  · intro w hw
    simpa only [hgradient] using hcompetitor w hw

end GammaMaximalityBridge
