import StressTensor
import GammaMaximalityBridge
import LocalizedStressBounds
import BornInfeldSubgradient
import Section33WeakEuler
import Section33Integrability
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Final packaging for Theorem 3.1

This module gives a concrete representative-level presentation of
`W^{1,∞}` on the square.  A map is represented by a Lipschitz function on
the closed square, a measurable essentially bounded gradient, and an a.e.
identification of that field with the classical gradient.  On a square this
is the standard continuous representative of a `W^{1,∞}` class.

The fixed-trace condition is not postulated as pointwise boundary equality.
Instead, it is witnessed by the assertion that `w - u` belongs to the
explicit smooth-density presentation of
`W^{1,1}_0 ∩ W^{1,∞}`.  Thus the test variation needed by the Euler
identity is part of the definition of the admissible class.
-/

open Filter MeasureTheory Set Topology

noncomputable section

namespace Theorem31

open BornInfeldSubgradient GammaMaximalityBridge MaximalityOfU StressTensor

abbrev PlaneVector := MaximalityOfU.Vector2

theorem cube_eq_openSquare (ell : ℝ) :
    MaximalityOfU.cube ell = StressTensor.openSquare ell := by
  ext z
  simp only [MaximalityOfU.cube, StressTensor.openSquare, mem_prod,
    mem_Ioo, mem_ofPred_eq, abs_lt]

/-- Essential boundedness on the square. -/
def EssentiallyBoundedOn (ell : ℝ) {E : Type*} [Norm E]
    (f : Plane → E) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᵐ z ∂(volume.restrict (MaximalityOfU.cube ell)), ‖f z‖ ≤ C

/-- Concrete representative-level presentation of `W^{1,∞}(Q_ell)`.
The Lipschitz representative prevents pathologies which would arise from
recording only an a.e. classical derivative. -/
structure W1InfinityMap (ell : ℝ) where
  toFun : Plane → ℝ
  gradient : Plane → PlaneVector
  lipschitzOn_closed :
    ∃ C : NNReal, LipschitzOnWith C toFun (closedSquare ell)
  gradient_aestronglyMeasurable : AEStronglyMeasurable gradient
    (volume.restrict (MaximalityOfU.cube ell))
  gradient_essentiallyBounded : EssentiallyBoundedOn ell gradient
  gradient_eq_classical_ae :
    ∀ᵐ z ∂(volume.restrict (MaximalityOfU.cube ell)),
      classicalGradient toFun z = gradient z

instance (ell : ℝ) : CoeFun (W1InfinityMap ell) (fun _ => Plane → ℝ) :=
  ⟨W1InfinityMap.toFun⟩

namespace W1InfinityMap

theorem continuousOn_closed {ell : ℝ} (w : W1InfinityMap ell) :
    ContinuousOn w.toFun (closedSquare ell) := by
  rcases w.lipschitzOn_closed with ⟨C, hC⟩
  exact hC.continuousOn

theorem toFun_essentiallyBounded {ell : ℝ} (w : W1InfinityMap ell) :
    EssentiallyBoundedOn ell w.toFun := by
  have hcompact := StressTensor.isCompact_closedSquare ell
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image w.continuousOn_closed.norm
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  filter_upwards [ae_restrict_mem (MaximalityOfU.cube_measurable ell)] with z hz
  have hzclosed : z ∈ closedSquare ell := by
    rw [cube_eq_openSquare] at hz
    exact ⟨hz.1.le, hz.2.le⟩
  exact (hC (mem_image_of_mem _ hzclosed)).trans (le_max_right _ _)

theorem toFun_aestronglyMeasurable {ell : ℝ} (w : W1InfinityMap ell) :
    AEStronglyMeasurable w.toFun
      (volume.restrict (MaximalityOfU.cube ell)) := by
  exact w.continuousOn_closed.aestronglyMeasurable_of_subset_isCompact
    (StressTensor.isCompact_closedSquare ell)
    (MaximalityOfU.cube_measurable ell) (by
      intro z hz
      rw [cube_eq_openSquare] at hz
      exact ⟨hz.1.le, hz.2.le⟩)

end W1InfinityMap

/-- The zero representative in the concrete `W^{1,∞}` model. -/
def zeroW1InfinityMap (ell : ℝ) : W1InfinityMap ell where
  toFun := fun _ => 0
  gradient := fun _ => 0
  lipschitzOn_closed :=
    ⟨0, (LipschitzWith.const' (0 : ℝ)).lipschitzOnWith⟩
  gradient_aestronglyMeasurable := aestronglyMeasurable_const
  gradient_essentiallyBounded := by
    refine ⟨0, le_rfl, ?_⟩
    filter_upwards with z
    simp
  gradient_eq_classical_ae := by
    filter_upwards with z
    simp [classicalGradient]

/-- Smooth compactly-supported approximation presentation of
`W^{1,1}_0(Q_ell) ∩ W^{1,∞}(Q_ell)`.  In addition to `W^{1,1}`
convergence, it records the a.e. gradient convergence and common `L^∞`
bound used in the manuscript's weak-* density step. -/
structure W11ZeroW1InfinityTest (ell : ℝ) where
  map : W1InfinityMap ell
  approximation : ℕ → Plane → ℝ
  approximation_smooth : ∀ n, ContDiff ℝ ⊤ (approximation n)
  approximation_compact : ∀ n, HasCompactSupport (approximation n)
  approximation_support : ∀ n,
    tsupport (approximation n) ⊆ MaximalityOfU.cube ell
  value_error_integrable : ∀ n,
    IntegrableOn (fun z => ‖approximation n z - map.toFun z‖)
      (MaximalityOfU.cube ell) volume
  gradient_error_integrable : ∀ n,
    IntegrableOn
      (fun z => ‖classicalGradient (approximation n) z - map.gradient z‖)
      (MaximalityOfU.cube ell) volume
  value_tendsto_L1 :
    Tendsto
      (fun n => ∫ z in MaximalityOfU.cube ell,
        ‖approximation n z - map.toFun z‖) atTop (nhds 0)
  gradient_tendsto_L1 :
    Tendsto
      (fun n => ∫ z in MaximalityOfU.cube ell,
        ‖classicalGradient (approximation n) z - map.gradient z‖)
      atTop (nhds 0)
  gradient_tendsto_ae :
    ∀ᵐ z ∂(volume.restrict (MaximalityOfU.cube ell)),
      Tendsto (fun n => classicalGradient (approximation n) z)
        atTop (nhds (map.gradient z))
  gradient_uniformly_bounded :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n,
      ∀ᵐ z ∂(volume.restrict (MaximalityOfU.cube ell)),
        ‖classicalGradient (approximation n) z‖ ≤ M

/-- The zero element of the explicit smooth-density presentation of
`W^{1,1}_0(Q_ell) ∩ W^{1,∞}(Q_ell)`.  Its constant-zero approximating
sequence makes trace reflexivity, and hence non-vacuity of each admissible
class containing an admissible base map, completely explicit. -/
def zeroW11ZeroW1InfinityTest (ell : ℝ) :
    W11ZeroW1InfinityTest ell where
  map := zeroW1InfinityMap ell
  approximation := fun _ _ => 0
  approximation_smooth := by
    intro n
    exact contDiff_const
  approximation_compact := by
    intro n
    exact HasCompactSupport.zero
  approximation_support := by
    intro n
    simp
  value_error_integrable := by
    intro n
    simp [zeroW1InfinityMap]
  gradient_error_integrable := by
    intro n
    simp [zeroW1InfinityMap, classicalGradient]
  value_tendsto_L1 := by
    simp [zeroW1InfinityMap]
  gradient_tendsto_L1 := by
    simp [zeroW1InfinityMap, classicalGradient]
  gradient_tendsto_ae := by
    filter_upwards with z
    simp [zeroW1InfinityMap, classicalGradient]
  gradient_uniformly_bounded := by
    refine ⟨0, le_rfl, ?_⟩
    intro n
    filter_upwards with z
    simp [classicalGradient]

/-- The pointwise admissibility condition from the paper. -/
def HasUnitGradient {ell : ℝ} (w : W1InfinityMap ell) : Prop :=
  ∀ᵐ z ∂(volume.restrict (MaximalityOfU.cube ell)),
    ‖w.gradient z‖ ≤ 1

/-- `w` and `u` have the same Sobolev trace precisely when `w-u` has an
explicit `W^{1,1}_0 ∩ W^{1,∞}` witness. -/
def HasSameSobolevTrace {ell : ℝ}
    (u w : W1InfinityMap ell) : Prop :=
  ∃ phi : W11ZeroW1InfinityTest ell,
    phi.map.toFun =ᵐ[volume.restrict (MaximalityOfU.cube ell)]
        (fun z => w.toFun z - u.toFun z) ∧
    phi.map.gradient =ᵐ[volume.restrict (MaximalityOfU.cube ell)]
        (fun z => w.gradient z - u.gradient z)

/-- Sobolev trace equality is reflexive, witnessed by the explicit zero
element of `W^{1,1}_0 ∩ W^{1,∞}`. -/
theorem hasSameSobolevTrace_self {ell : ℝ} (w : W1InfinityMap ell) :
    HasSameSobolevTrace w w := by
  refine ⟨zeroW11ZeroW1InfinityTest ell, ?_, ?_⟩
  · filter_upwards with z
    simp [zeroW11ZeroW1InfinityTest, zeroW1InfinityMap]
  · filter_upwards with z
    simp [zeroW11ZeroW1InfinityTest, zeroW1InfinityMap]

def DirichletClass {ell : ℝ} (u : W1InfinityMap ell) :
    Set (W1InfinityMap ell) :=
  {w | HasUnitGradient w ∧ HasSameSobolevTrace u w}

/-- Every admissible base map is itself a competitor in its Dirichlet
class; in particular, the class used in maximality is nonempty. -/
theorem mem_dirichletClass_self {ell : ℝ} {u : W1InfinityMap ell}
    (hu : HasUnitGradient u) : u ∈ DirichletClass u :=
  ⟨hu, hasSameSobolevTrace_self u⟩

def BornInfeldEnergy (q : ℝ) {ell : ℝ} (w : W1InfinityMap ell) : ℝ :=
  Energy (volume.restrict (MaximalityOfU.cube ell))
    (bornInfeldDensity q) w.gradient

def IsBornInfeldMaximizer (q : ℝ) {ell : ℝ}
    (u : W1InfinityMap ell) : Prop :=
  u ∈ DirichletClass u ∧ ∀ w, w ∈ DirichletClass u →
    BornInfeldEnergy q w ≤ BornInfeldEnergy q u

/-! ## The unconditional analytic/geometric core -/

structure GeometricCore (P : Params) where
  rx : ℝ
  ry : ℝ
  rx_pos : 0 < rx
  ry_pos : 0 < ry
  K : CKOutcome P (reconstructionBox rx ry) ry
  L : CompactSquareLocalization P K.gamma (reconstructionBox rx ry)
  stress_divergence_off_axis : ∀ {w : Plane},
    w ∈ openSquare L.ell → w.2 ≠ 0 →
      energyGradientStressDivergence P K.gamma w.1 w.2 = 0
  horizontal_is_maximal : IsMaximallyExtendedLightSegment
    (openSquare L.ell) (fun w => ansatz K.gamma w.1 w.2)
    (horizontalLeft L.ell) (horizontalRight L.ell)
  unique_maximal : ∀ {a b : Plane},
    IsMaximallyExtendedLightSegment
      (openSquare L.ell) (fun w => ansatz K.gamma w.1 w.2) a b →
    closedSegment a b = horizontalDiameter L.ell
  gamma_even : ∀ w ∈ reconstructionBox rx ry,
    K.gamma w.1 (-w.2) = K.gamma w.1 w.2

theorem nonempty_geometricCore (P : Params) : Nonempty (GeometricCore P) := by
  rcases CompleteArgument.exists_complete_argument P with
    ⟨rx, ry, hrx, hry, K, L, hdiv, hhorizontal, hunique, heven⟩
  exact ⟨⟨rx, ry, hrx, hry, K, L, hdiv, hhorizontal, hunique, heven⟩⟩

noncomputable def canonicalGeometricCore (P : Params) : GeometricCore P :=
  Classical.choice (nonempty_geometricCore P)

noncomputable def Params.ofQ (q : ℝ) (hq1 : 1 < q) (hq2 : q < 2) : Params where
  p := conjugateExponent q
  q := q
  one_lt_q := hq1
  q_lt_two := hq2
  two_lt_p := conjugateExponent_gt_two hq1 hq2
  holder := by
    have hq0 : q ≠ 0 := ne_of_gt (lt_trans (by norm_num) hq1)
    have hqm1 : q - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
    rw [conjugateExponent]
    field_simp [hq0, hqm1]
    ring

@[simp] theorem Params.ofQ_q (q : ℝ) (hq1 : 1 < q) (hq2 : q < 2) :
    (Params.ofQ q hq1 hq2).q = q := rfl

/-! ## The canonical Sobolev candidate -/

theorem ansatzMap_analyticOnNhd_closedSquare
    {P : Params} (G : GeometricCore P) :
    AnalyticOnNhd ℝ (ansatzMap G.K.gamma) (closedSquare G.L.ell) := by
  intro w hw
  have hgamma : AnalyticAt ℝ (uncurried G.K.gamma) w :=
    G.K.solution.1 w (G.L.closed_subset_domain hw)
  change AnalyticAt ℝ
    ((fun z : Plane => z.1) +
      (fun z : Plane => z.2) ^ 2 * uncurried G.K.gamma) w
  exact analyticAt_fst.add ((analyticAt_snd.pow 2).mul hgamma)

theorem classicalGradient_ansatzMap
    {P : Params} (G : GeometricCore P) {w : Plane}
    (hw : w ∈ closedSquare G.L.ell) :
    classicalGradient (ansatzMap G.K.gamma) w =
      ansatzGradientField G.K.gamma w := by
  have hdiff := differentiableAt_coordinateSlices_of_analyticAt
    (G.K.solution.1 w (G.L.closed_subset_domain hw))
  have hactual := actualAnsatzGradient_eq_ansatzGradient hdiff.1 hdiff.2
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  ext i
  fin_cases i
  · simpa [classicalGradient, ansatzMap, ansatzGradientField,
      actualAnsatzGradient, ansatzGradient, partialX,
      gamma1Field] using congrArg Prod.fst hactual
  · simpa [classicalGradient, ansatzMap, ansatzGradientField,
      actualAnsatzGradient, ansatzGradient, partialY,
      gamma2Field] using congrArg Prod.snd hactual

theorem ansatzGradientField_norm_sq
    (gamma : ℝ → ℝ → ℝ) (z : Plane) :
    ‖ansatzGradientField gamma z‖ ^ 2 =
      normSq (ansatzGradient z.2 (jetOf gamma z.1 z.2)) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rcases z with ⟨x, y⟩
  simp [ansatzGradientField, normSq, ansatzGradient,
    gamma1Field, gamma2Field]

theorem ansatzGradient_norm_le_one
    {P : Params} (G : GeometricCore P) {w : Plane}
    (hw : w ∈ closedSquare G.L.ell) :
    ‖ansatzGradientField G.K.gamma w‖ ≤ 1 := by
  have hdiff := differentiableAt_coordinateSlices_of_analyticAt
    (G.K.solution.1 w (G.L.closed_subset_domain hw))
  have hactual := actualAnsatzGradient_eq_ansatzGradient hdiff.1 hdiff.2
  have hsquared : ‖ansatzGradientField G.K.gamma w‖ ^ 2 ≤ 1 := by
    rw [ansatzGradientField_norm_sq, ← hactual]
    by_cases hy : w.2 = 0
    · have hw0 : (w.1, 0) ∈ closedSquare G.L.ell :=
        ⟨hw.1, by simpa using G.L.ell_pos.le⟩
      simpa only [hy] using
        (G.L.normSq_actualAnsatzGradient_axis G.K.solution.1 hw0).le
    · exact (G.L.normSq_actualAnsatzGradient_lt_one
        G.K.solution.1 hw hy).le
  rw [← sq_le_one_iff₀ (norm_nonneg _)]
  simpa using hsquared

theorem ansatzGradient_norm_lt_one_off_axis
    {P : Params} (G : GeometricCore P) {w : Plane}
    (hw : w ∈ openSquare G.L.ell) (hy : w.2 ≠ 0) :
    ‖ansatzGradientField G.K.gamma w‖ < 1 := by
  have hwclosed : w ∈ closedSquare G.L.ell := ⟨hw.1.le, hw.2.le⟩
  have hdiff := differentiableAt_coordinateSlices_of_analyticAt
    (G.K.solution.1 w (G.L.closed_subset_domain hwclosed))
  have hactual := actualAnsatzGradient_eq_ansatzGradient hdiff.1 hdiff.2
  have hsquared : ‖ansatzGradientField G.K.gamma w‖ ^ 2 < 1 := by
    rw [ansatzGradientField_norm_sq, ← hactual]
    exact G.L.normSq_actualAnsatzGradient_lt_one
      G.K.solution.1 hwclosed hy
  rw [← sq_lt_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  simpa using hsquared

theorem convex_closedSquare (ell : ℝ) :
    Convex ℝ (closedSquare ell) := by
  have heq : closedSquare ell =
      Icc (-ell) ell ×ˢ Icc (-ell) ell := by
    ext z
    simp only [closedSquare, mem_ofPred_eq, mem_prod, mem_Icc, abs_le]
  rw [heq]
  exact (convex_Icc (-ell) ell).prod (convex_Icc (-ell) ell)

theorem ansatzMap_exists_lipschitzOn_closed
    {P : Params} (G : GeometricCore P) :
    ∃ C : NNReal,
      LipschitzOnWith C (ansatzMap G.K.gamma) (closedSquare G.L.ell) := by
  have hcontDiff : ContDiffOn ℝ 1 (ansatzMap G.K.gamma)
      (closedSquare G.L.ell) :=
    (ansatzMap_analyticOnNhd_closedSquare G).contDiffOn_of_completeSpace
  exact hcontDiff.exists_lipschitzOnWith one_ne_zero
    (convex_closedSquare G.L.ell) (isCompact_closedSquare G.L.ell)

theorem ansatzGradientField_continuousOn_closed
    {P : Params} (G : GeometricCore P) :
    ContinuousOn (ansatzGradientField G.K.gamma)
      (closedSquare G.L.ell) := by
  have hfields := localized_factor_fields_continuousOn
    G.L G.K.solution.1
  have hpair : ContinuousOn
      (fun w : Plane =>
        (gamma1Field G.K.gamma w.1 w.2,
          2 * w.2 * gamma2Field G.K.gamma w.1 w.2))
      (closedSquare G.L.ell) := by
    exact hfields.2.1.prodMk
      ((continuousOn_const.mul continuousOn_snd).mul hfields.2.2)
  have hconvert : Continuous pairToVector := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    fun_prop
  change ContinuousOn
    (fun w : Plane => (EuclideanSpace.equiv (Fin 2) ℝ).symm
      ![gamma1Field G.K.gamma w.1 w.2,
        2 * w.2 * gamma2Field G.K.gamma w.1 w.2])
    (closedSquare G.L.ell)
  simpa only [pairToVector, Function.comp_def] using
    hconvert.comp_continuousOn hpair

/-- The analytic ansatz, with its actual classical gradient, is a concrete
`W^{1,∞}` representative on the localized square. -/
noncomputable def ansatzW1InfinityMap
    {P : Params} (G : GeometricCore P) : W1InfinityMap G.L.ell where
  toFun := ansatzMap G.K.gamma
  gradient := ansatzGradientField G.K.gamma
  lipschitzOn_closed := ansatzMap_exists_lipschitzOn_closed G
  gradient_aestronglyMeasurable :=
    (ansatzGradientField_continuousOn_closed G).aestronglyMeasurable_of_subset_isCompact
      (isCompact_closedSquare G.L.ell)
      (MaximalityOfU.cube_measurable G.L.ell) (by
        intro z hz
        rw [cube_eq_openSquare] at hz
        exact ⟨hz.1.le, hz.2.le⟩)
  gradient_essentiallyBounded := by
    refine ⟨1, by norm_num, ?_⟩
    filter_upwards [ae_restrict_mem
      (MaximalityOfU.cube_measurable G.L.ell)] with z hz
    apply ansatzGradient_norm_le_one G
    rw [cube_eq_openSquare] at hz
    exact ⟨hz.1.le, hz.2.le⟩
  gradient_eq_classical_ae := by
    filter_upwards [ae_restrict_mem
      (MaximalityOfU.cube_measurable G.L.ell)] with z hz
    apply classicalGradient_ansatzMap G
    rw [cube_eq_openSquare] at hz
    exact ⟨hz.1.le, hz.2.le⟩

theorem ansatzW1InfinityMap_hasUnitGradient
    {P : Params} (G : GeometricCore P) :
    HasUnitGradient (ansatzW1InfinityMap G) := by
  filter_upwards [ae_restrict_mem
    (MaximalityOfU.cube_measurable G.L.ell)] with z hz
  apply ansatzGradient_norm_le_one G
  rw [cube_eq_openSquare] at hz
  exact ⟨hz.1.le, hz.2.le⟩

@[simp] theorem ansatzW1InfinityMap_toFun
    {P : Params} (G : GeometricCore P) :
    (ansatzW1InfinityMap G).toFun = ansatzMap G.K.gamma := rfl

@[simp] theorem ansatzW1InfinityMap_gradient
    {P : Params} (G : GeometricCore P) :
    (ansatzW1InfinityMap G).gradient =
      ansatzGradientField G.K.gamma := rfl

/-! ## The concrete a.e. Born--Infeld subgradient -/

theorem pairToVector_actualAnsatzGradient_eq
    {P : Params} (G : GeometricCore P) {w : Plane}
    (hw : w ∈ closedSquare G.L.ell) :
    pairToVector (actualAnsatzGradient G.K.gamma w.1 w.2) =
      ansatzGradientField G.K.gamma w := by
  have hdiff := differentiableAt_coordinateSlices_of_analyticAt
    (G.K.solution.1 w (G.L.closed_subset_domain hw))
  have hactual := actualAnsatzGradient_eq_ansatzGradient hdiff.1 hdiff.2
  simpa [pairToVector, ansatzGradientField, ansatzGradient,
    gamma1Field, gamma2Field] using
    congrArg pairToVector hactual

theorem stressField_eq_pairToVector_energyGradientStress
    {P : Params} (G : GeometricCore P) {w : Plane}
    (hw : w ∈ closedSquare G.L.ell) (hy : w.2 ≠ 0) :
    stressField P G.K.gamma w =
      pairToVector (energyGradientStress P G.K.gamma w.1 w.2) := by
  rcases w with ⟨x, y⟩
  have hdiff := differentiableAt_coordinateSlices_of_analyticAt
    (G.K.solution.1 (x, y) (G.L.closed_subset_domain hw))
  have henergy := energyGradientStress_eq_singularStress_of_inU
    (G.L.jet_inU (x, y) hw) hy hdiff.1 hdiff.2
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  ext i
  fin_cases i
  · change (EuclideanSpace.equiv (Fin 2) ℝ)
      (stressField P G.K.gamma (x, y)) 0 =
        (EuclideanSpace.equiv (Fin 2) ℝ)
          (pairToVector (energyGradientStress P G.K.gamma x y)) 0
    rw [stressField_coord_zero_off_axis P G.K.gamma x y hy]
    simpa [pairToVector, singularStress] using
      (congrArg Prod.fst henergy).symm
  · change (EuclideanSpace.equiv (Fin 2) ℝ)
      (stressField P G.K.gamma (x, y)) 1 =
        (EuclideanSpace.equiv (Fin 2) ℝ)
          (pairToVector (energyGradientStress P G.K.gamma x y)) 1
    rw [stressField_coord_one_off_axis P G.K.gamma x y hy]
    simpa [pairToVector, singularStress] using
      (congrArg Prod.snd henergy).symm

theorem stressField_isSubgradientAtOn
    {P : Params} (G : GeometricCore P) {w : Plane}
    (hw : w ∈ closedSquare G.L.ell) (hy : w.2 ≠ 0) :
    IsSubgradientAtOn (closedUnitBall : Set PlaneVector)
      (tildeBornInfeldDensity P.q)
      (ansatzGradientField G.K.gamma w) (stressField P G.K.gamma w) := by
  have hstrict := G.L.normSq_actualAnsatzGradient_lt_one
    G.K.solution.1 hw hy
  have hsub := energyGradientStress_isSubgradientAtOn
    P G.K.gamma w.1 w.2 hstrict
  rw [pairToVector_actualAnsatzGradient_eq G hw,
    ← stressField_eq_pairToVector_energyGradientStress G hw hy] at hsub
  exact hsub

theorem ae_snd_ne_zero :
    ∀ᵐ z : Plane ∂volume, z.2 ≠ 0 := by
  rw [Measure.volume_eq_prod]
  rw [Measure.ae_prod_iff_ae_ae]
  · filter_upwards with x
    exact volume.ae_ne 0
  · exact (measurable_snd (measurableSet_singleton 0)).compl

theorem stressField_isSubgradientAtOn_ae
    {P : Params} (G : GeometricCore P) :
    ∀ᵐ w ∂(volume.restrict (MaximalityOfU.cube G.L.ell)),
      IsSubgradientAtOn (closedUnitBall : Set PlaneVector)
        (tildeBornInfeldDensity P.q)
        (ansatzGradientField G.K.gamma w) (stressField P G.K.gamma w) := by
  have hoff : ∀ᵐ w : Plane
      ∂(volume.restrict (MaximalityOfU.cube G.L.ell)), w.2 ≠ 0 :=
    ae_snd_ne_zero.filter_mono (ae_mono Measure.restrict_le_self)
  filter_upwards [ae_restrict_mem
    (MaximalityOfU.cube_measurable G.L.ell), hoff] with w hw hy
  apply stressField_isSubgradientAtOn G _ hy
  rw [cube_eq_openSquare] at hw
  exact ⟨hw.1.le, hw.2.le⟩

/-! ## Integrability hypotheses discharged from the concrete class -/

theorem ansatz_tildeDensity_integrable
    {P : Params} (G : GeometricCore P) :
    Integrable
      (fun z => tildeBornInfeldDensity P.q
        ((ansatzW1InfinityMap G).gradient z))
      (volume.restrict (MaximalityOfU.cube G.L.ell)) := by
  exact Section33Integrability.tildeBornInfeldDensity_integrableOn_cube
    P.q_pos (ansatzW1InfinityMap G).gradient_aestronglyMeasurable
      (ansatzW1InfinityMap_hasUnitGradient G)

theorem competitor_tildeDensity_integrable
    {P : Params} (G : GeometricCore P) {w : W1InfinityMap G.L.ell}
    (hw : HasUnitGradient w) :
    Integrable (fun z => tildeBornInfeldDensity P.q (w.gradient z))
      (volume.restrict (MaximalityOfU.cube G.L.ell)) := by
  exact Section33Integrability.tildeBornInfeldDensity_integrableOn_cube
    P.q_pos w.gradient_aestronglyMeasurable hw

theorem stress_variation_integrable
    {P : Params} (G : GeometricCore P) {w : W1InfinityMap G.L.ell}
    (hw : HasUnitGradient w) :
    IntegrableOn
      (fun z => inner ℝ (stressField P G.K.gamma z)
        (w.gradient z - (ansatzW1InfinityMap G).gradient z))
      (MaximalityOfU.cube G.L.ell) volume := by
  exact Section33Integrability.inner_stress_sub_integrableOn_cube_of_unit_bounds
    (localized_stressField_integrableOn_cube G.L G.K.solution.1)
    w.gradient_aestronglyMeasurable
    (ansatzW1InfinityMap G).gradient_aestronglyMeasurable hw
    (ansatzW1InfinityMap_hasUnitGradient G)

/-- Once the dense weak Euler identity is available, every remaining
variational hypothesis is supplied by the concrete Sobolev class, the
localized stress estimate, and the a.e. subgradient theorem above. -/
theorem ansatz_isBornInfeldMaximizer_of_weakEuler
    {P : Params} (G : GeometricCore P)
    (hEuler : ∀ phi : W11ZeroW1InfinityTest G.L.ell,
      (∫ z in MaximalityOfU.cube G.L.ell,
        inner ℝ (stressField P G.K.gamma z) (phi.map.gradient z)) = 0) :
    IsBornInfeldMaximizer P.q (ansatzW1InfinityMap G) := by
  refine ⟨mem_dirichletClass_self
    (ansatzW1InfinityMap_hasUnitGradient G), ?_⟩
  intro w hw
  rcases hw.2 with ⟨phi, _hvalue, hgradient⟩
  have hweakEuler :
      (∫ z in MaximalityOfU.cube G.L.ell,
        inner ℝ (stressField P G.K.gamma z)
          (w.gradient z - (ansatzW1InfinityMap G).gradient z)) = 0 := by
    calc
      (∫ z in MaximalityOfU.cube G.L.ell,
          inner ℝ (stressField P G.K.gamma z)
            (w.gradient z - (ansatzW1InfinityMap G).gradient z)) =
          ∫ z in MaximalityOfU.cube G.L.ell,
            inner ℝ (stressField P G.K.gamma z)
              (phi.map.gradient z) := by
        apply integral_congr_ae
        exact hgradient.mono fun z hz => by
          exact congrArg (fun v => inner ℝ (stressField P G.K.gamma z) v)
            hz.symm
      _ = 0 := hEuler phi
  have hdomain :
      ∀ᵐ z ∂(volume.restrict (MaximalityOfU.cube G.L.ell)),
        w.gradient z ∈ (closedUnitBall : Set PlaneVector) := by
    simpa only [HasUnitGradient, closedUnitBall, mem_ofPred_eq] using hw.1
  have hminimum := energy_le_of_subgradientOn_and_weakEuler
    (ansatz_tildeDensity_integrable G)
    (competitor_tildeDensity_integrable G hw.1)
    (stress_variation_integrable G hw.1)
    hdomain (stressField_isSubgradientAtOn_ae G) hweakEuler
  simpa only [BornInfeldEnergy, tildeBornInfeldDensity, neg_neg] using
    (negEnergy_reverses_inequality hminimum)

end Theorem31
