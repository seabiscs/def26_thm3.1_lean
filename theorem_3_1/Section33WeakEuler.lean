import StressTensor
import GammaMaximalityBridge
import LocalizedStressBounds
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The removable light-ray interface

This file supplies the part of Section 3.3 which is not pointwise: test
functions, excision of the horizontal axis, and passage to the Sobolev test
class.  The definitions deliberately record a concrete smooth-density
presentation of `W¹₀,¹ ∩ W¹,∞`; this avoids postulating a trace operator while
retaining exactly the approximation used in the manuscript.
-/

open Filter MeasureTheory Set Topology

noncomputable section

namespace Theorem31

open GammaMaximalityBridge MaximalityOfU StressTensor

abbrev Plane := StressTensor.Point

/-- The classical coordinate gradient, in the Euclidean two-space used by
the measure-theoretic formalization. -/
def classicalGradient (f : Plane → ℝ) : Plane → Vector2 :=
  fun z => (EuclideanSpace.equiv (Fin 2) ℝ).symm
    ![deriv (fun x => f (x, z.2)) z.1,
      deriv (fun y => f (z.1, y)) z.2]

@[simp] theorem classicalGradient_apply_zero (f : Plane → ℝ) (z : Plane) :
    (EuclideanSpace.equiv (Fin 2) ℝ) (classicalGradient f z) 0 =
      deriv (fun x => f (x, z.2)) z.1 := by
  simp [classicalGradient]

@[simp] theorem classicalGradient_apply_one (f : Plane → ℝ) (z : Plane) :
    (EuclideanSpace.equiv (Fin 2) ℝ) (classicalGradient f z) 1 =
      deriv (fun y => f (z.1, y)) z.2 := by
  simp [classicalGradient]

/-- A `C¹` test function whose (closed) support lies inside the open
square.  This is the concrete `C¹_c(Q_ℓ)` class used in the excision
argument. -/
structure SmoothTest (ell : ℝ) where
  toFun : Plane → ℝ
  contDiff : ContDiff ℝ 1 toFun
  support_subset : Function.support toFun ⊆ cube ell

instance (ell : ℝ) : CoeFun (SmoothTest ell) (fun _ => Plane → ℝ) :=
  ⟨SmoothTest.toFun⟩

namespace SmoothTest

variable {ell : ℝ} (phi : SmoothTest ell)

theorem differentiableAt (z : Plane) : DifferentiableAt ℝ phi z :=
  phi.contDiff.differentiable_one z

theorem continuous (z : Plane) : ContinuousAt phi z :=
  (phi.differentiableAt z).continuousAt

theorem eq_zero_of_not_mem_cube {z : Plane} (hz : z ∉ cube ell) : phi z = 0 := by
  by_contra hne
  exact hz (phi.support_subset hne)

theorem eq_zero_left (y : ℝ) : phi (-ell, y) = 0 := by
  apply phi.eq_zero_of_not_mem_cube
  simp [cube]

theorem eq_zero_right (y : ℝ) : phi (ell, y) = 0 := by
  apply phi.eq_zero_of_not_mem_cube
  simp [cube]

theorem eq_zero_bottom (x : ℝ) : phi (x, -ell) = 0 := by
  apply phi.eq_zero_of_not_mem_cube
  simp [cube]

theorem eq_zero_top (x : ℝ) : phi (x, ell) = 0 := by
  apply phi.eq_zero_of_not_mem_cube
  simp [cube]

theorem measurable_gradient : StronglyMeasurable (classicalGradient phi) := by
  have hfd : Continuous (fderiv ℝ phi) :=
    phi.contDiff.continuous_fderiv one_ne_zero
  have hcoord0 : Continuous (fun z : Plane => fderiv ℝ phi z (1, 0)) :=
    hfd.clm_apply continuous_const
  have hcoord1 : Continuous (fun z : Plane => fderiv ℝ phi z (0, 1)) :=
    hfd.clm_apply continuous_const
  have heq0 : (fun z : Plane => deriv (fun x => phi (x, z.2)) z.1) =
      fun z => fderiv ℝ phi z (1, 0) := by
    funext z
    have hpath : HasDerivAt (fun x : ℝ => (x, z.2)) (1, 0) z.1 :=
      (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
    change deriv (phi.toFun ∘ fun x : ℝ => (x, z.2)) z.1 = _
    exact ((phi.differentiableAt z).hasFDerivAt.comp_hasDerivAt z.1 hpath).deriv
  have heq1 : (fun z : Plane => deriv (fun y => phi (z.1, y)) z.2) =
      fun z => fderiv ℝ phi z (0, 1) := by
    funext z
    have hpath : HasDerivAt (fun y : ℝ => (z.1, y)) (0, 1) z.2 :=
      (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
    change deriv (phi.toFun ∘ fun y : ℝ => (z.1, y)) z.2 = _
    exact ((phi.differentiableAt z).hasFDerivAt.comp_hasDerivAt z.2 hpath).deriv
  rw [show classicalGradient phi = fun z =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm
        ![(fun z => deriv (fun x => phi (x, z.2)) z.1) z,
          (fun z => deriv (fun y => phi (z.1, y)) z.2) z] by rfl,
    heq0, heq1]
  apply Continuous.stronglyMeasurable
  apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
  fun_prop

theorem continuous_gradient : Continuous (classicalGradient phi) := by
  have hfd : Continuous (fderiv ℝ phi) :=
    phi.contDiff.continuous_fderiv one_ne_zero
  have hcoord0 : Continuous (fun z : Plane => fderiv ℝ phi z (1, 0)) :=
    hfd.clm_apply continuous_const
  have hcoord1 : Continuous (fun z : Plane => fderiv ℝ phi z (0, 1)) :=
    hfd.clm_apply continuous_const
  have heq0 : (fun z : Plane => deriv (fun x => phi (x, z.2)) z.1) =
      fun z => fderiv ℝ phi z (1, 0) := by
    funext z
    have hpath : HasDerivAt (fun x : ℝ => (x, z.2)) (1, 0) z.1 :=
      (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
    change deriv (phi.toFun ∘ fun x : ℝ => (x, z.2)) z.1 = _
    exact ((phi.differentiableAt z).hasFDerivAt.comp_hasDerivAt z.1 hpath).deriv
  have heq1 : (fun z : Plane => deriv (fun y => phi (z.1, y)) z.2) =
      fun z => fderiv ℝ phi z (0, 1) := by
    funext z
    have hpath : HasDerivAt (fun y : ℝ => (z.1, y)) (0, 1) z.2 :=
      (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
    change deriv (phi.toFun ∘ fun y : ℝ => (z.1, y)) z.2 = _
    exact ((phi.differentiableAt z).hasFDerivAt.comp_hasDerivAt z.2 hpath).deriv
  rw [show classicalGradient phi = fun z =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm
        ![(fun z => deriv (fun x => phi (x, z.2)) z.1) z,
          (fun z => deriv (fun y => phi (z.1, y)) z.2) z] by rfl,
    heq0, heq1]
  apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
  fun_prop

/-- A smooth test and its classical gradient admit honest pointwise bounds
on the closed square.  We use pointwise (rather than merely essential)
bounds so that the traces on the two excision lines are covered directly. -/
theorem exists_abs_bound_on_closedSquare :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ closedSquare ell, |phi z| ≤ M := by
  have hcont : ContinuousOn (fun z : Plane => |phi z|) (closedSquare ell) :=
    phi.contDiff.continuous.abs.continuousOn
  obtain ⟨C, hC⟩ :=
    (isCompact_closedSquare ell).bddAbove_image hcont
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro z hz
  exact (hC (mem_image_of_mem _ hz)).trans (le_max_right _ _)

theorem exists_gradient_norm_bound_on_closedSquare :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ closedSquare ell, ‖classicalGradient phi z‖ ≤ M := by
  have hcont : ContinuousOn (fun z : Plane => ‖classicalGradient phi z‖)
      (closedSquare ell) := phi.continuous_gradient.norm.continuousOn
  obtain ⟨C, hC⟩ :=
    (isCompact_closedSquare ell).bddAbove_image hcont
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro z hz
  exact (hC (mem_image_of_mem _ hz)).trans (le_max_right _ _)

end SmoothTest

/-! ## Off-axis regularity of the factored stress -/

theorem analyticAt_partialX_field
    {gamma : ℝ → ℝ → ℝ} {w : Plane}
    (hgamma : AnalyticAt ℝ (uncurried gamma) w) :
    AnalyticAt ℝ (fun z : Plane => partialX gamma z.1 z.2) w := by
  let f : Plane → ℝ := uncurried gamma
  let ex : Plane := (1, 0)
  have hfd : AnalyticAt ℝ (fderiv ℝ f) w := by
    simpa only [f] using hgamma.fderiv
  have heval : AnalyticAt ℝ (fun z => fderiv ℝ f z ex) w :=
    (hfd.contDiffAt.clm_apply contDiffAt_const).analyticAt
  have hev : ∀ᶠ z in nhds w, AnalyticAt ℝ f z := by
    simpa only [f] using hgamma.eventually_analyticAt
  apply heval.congr
  filter_upwards [hev] with z hz
  simpa only [f, ex] using
    (partialX_eq_fderiv_uncurried hz.differentiableAt).symm

theorem analyticAt_partialY_field
    {gamma : ℝ → ℝ → ℝ} {w : Plane}
    (hgamma : AnalyticAt ℝ (uncurried gamma) w) :
    AnalyticAt ℝ (fun z : Plane => partialY gamma z.1 z.2) w := by
  let f : Plane → ℝ := uncurried gamma
  let ey : Plane := (0, 1)
  have hfd : AnalyticAt ℝ (fderiv ℝ f) w := by
    simpa only [f] using hgamma.fderiv
  have heval : AnalyticAt ℝ (fun z => fderiv ℝ f z ey) w :=
    (hfd.contDiffAt.clm_apply contDiffAt_const).analyticAt
  have hev : ∀ᶠ z in nhds w, AnalyticAt ℝ f z := by
    simpa only [f] using hgamma.eventually_analyticAt
  apply heval.congr
  filter_upwards [hev] with z hz
  simpa only [f, ey] using
    (partialY_eq_fderiv_uncurried hz.differentiableAt).symm

theorem analyticAt_gamma1Field
    {gamma : ℝ → ℝ → ℝ} {w : Plane}
    (hgamma : AnalyticAt ℝ (uncurried gamma) w) :
    AnalyticAt ℝ (fun z : Plane => gamma1Field gamma z.1 z.2) w := by
  have hdx := analyticAt_partialX_field hgamma
  change AnalyticAt ℝ
    (fun z : Plane => 1 + z.2 ^ 2 * partialX gamma z.1 z.2) w
  exact analyticAt_const.add ((analyticAt_snd.pow 2).mul hdx)

theorem analyticAt_gamma2Field
    {gamma : ℝ → ℝ → ℝ} {w : Plane}
    (hgamma : AnalyticAt ℝ (uncurried gamma) w) :
    AnalyticAt ℝ (fun z : Plane => gamma2Field gamma z.1 z.2) w := by
  have hdy := analyticAt_partialY_field hgamma
  change AnalyticAt ℝ
    (fun z : Plane => uncurried gamma z + z.2 * partialY gamma z.1 z.2 / 2) w
  exact hgamma.add (analyticAt_snd.mul hdy).div_const

theorem analyticAt_gamma0Field
    {gamma : ℝ → ℝ → ℝ} {w : Plane}
    (hgamma : AnalyticAt ℝ (uncurried gamma) w) :
    AnalyticAt ℝ (fun z : Plane => gamma0Field gamma z.1 z.2) w := by
  have hdx := analyticAt_partialX_field hgamma
  have hg2 := analyticAt_gamma2Field hgamma
  change AnalyticAt ℝ (fun z : Plane =>
    2 * partialX gamma z.1 z.2 +
      z.2 ^ 2 * partialX gamma z.1 z.2 ^ 2 +
      4 * gamma2Field gamma z.1 z.2 ^ 2) w
  exact (analyticAt_const.mul hdx).add
    ((analyticAt_snd.pow 2).mul (hdx.pow 2)) |>.add
      (analyticAt_const.mul (hg2.pow 2))

theorem analyticAt_scalarField_of_inU
    {P : Params} {gamma : ℝ → ℝ → ℝ} {w : Plane}
    (hgamma : AnalyticAt ℝ (uncurried gamma) w)
    (hU : InU P w.1 w.2 (jetOf gamma w.1 w.2)) :
    AnalyticAt ℝ (fun z : Plane => scalarField P gamma z.1 z.2) w := by
  have hmap : AnalyticAt ℝ
      (fun z : Plane => (z.2, gamma0Field gamma z.1 z.2)) w :=
    analyticAt_snd.prod (analyticAt_gamma0Field hgamma)
  have hS : AnalyticAt ℝ (stildeUncurried P)
      (w.2, gamma0Field gamma w.1 w.2) :=
    (inV_gamma0_of_inU hU).analyticAt_Stilde
  simpa only [Function.comp_def, stildeUncurried, scalarField_eq_Stilde] using
    (AnalyticAt.comp (x := w)
      (f := fun z : Plane => (z.2, gamma0Field gamma z.1 z.2)) hS hmap)

theorem differentiableAt_singularDenominator_off_axis
    (P : Params) {w : Plane} (hy : w.2 ≠ 0) :
    DifferentiableAt ℝ
      (fun z : Plane => singularDenominator P z.2) w := by
  have habs : HasDerivAt (fun y : ℝ => |y|)
      (SignType.sign w.2 : ℝ) w.2 := hasDerivAt_abs hy
  have hpow := habs.rpow_const (p := 2 / P.p)
    (Or.inl (abs_ne_zero.mpr hy))
  exact hpow.differentiableAt.comp w differentiableAt_snd

theorem differentiableAt_singularStressX_off_axis
    {P : Params} {gamma : ℝ → ℝ → ℝ} {w : Plane}
    (hgamma : AnalyticAt ℝ (uncurried gamma) w)
    (hU : InU P w.1 w.2 (jetOf gamma w.1 w.2))
    (hy : w.2 ≠ 0) :
    DifferentiableAt ℝ
      (fun z : Plane => singularStressX P gamma z.1 z.2) w := by
  have hscalar := (analyticAt_scalarField_of_inU hgamma hU).differentiableAt
  have hg1 := (analyticAt_gamma1Field hgamma).differentiableAt
  have hdenom := differentiableAt_singularDenominator_off_axis P hy
  have hdenom0 : singularDenominator P w.2 ≠ 0 :=
    (Real.rpow_pos_of_pos (abs_pos.mpr hy) (2 / P.p)).ne'
  exact (hscalar.mul hg1).mul (hdenom.inv hdenom0)

theorem differentiableAt_singularStressY_off_axis
    {P : Params} {gamma : ℝ → ℝ → ℝ} {w : Plane}
    (hgamma : AnalyticAt ℝ (uncurried gamma) w)
    (hU : InU P w.1 w.2 (jetOf gamma w.1 w.2))
    (hy : w.2 ≠ 0) :
    DifferentiableAt ℝ
      (fun z : Plane => singularStressY P gamma z.1 z.2) w := by
  have hscalar := (analyticAt_scalarField_of_inU hgamma hU).differentiableAt
  have hg2 := (analyticAt_gamma2Field hgamma).differentiableAt
  have hdenom := differentiableAt_singularDenominator_off_axis P hy
  have hdenom0 : singularDenominator P w.2 ≠ 0 :=
    (Real.rpow_pos_of_pos (abs_pos.mpr hy) (2 / P.p)).ne'
  have hratio : DifferentiableAt ℝ
      (fun z : Plane => z.2 / singularDenominator P z.2) w :=
    differentiableAt_snd.mul (hdenom.inv hdenom0)
  exact (differentiableAt_const (2 : ℝ)).mul
    (hratio.mul (hscalar.mul hg2))

/-! ## The product field used in integration by parts -/

def factoredPairing (P : Params) (gamma : ℝ → ℝ → ℝ)
    (phi : Plane → ℝ) (z : Plane) : ℝ :=
  singularStressX P gamma z.1 z.2 *
      deriv (fun x => phi (x, z.2)) z.1 +
    singularStressY P gamma z.1 z.2 *
      deriv (fun y => phi (z.1, y)) z.2

def fluxX (P : Params) (gamma : ℝ → ℝ → ℝ)
    (phi : Plane → ℝ) (z : Plane) : ℝ :=
  singularStressX P gamma z.1 z.2 * phi z

def fluxY (P : Params) (gamma : ℝ → ℝ → ℝ)
    (phi : Plane → ℝ) (z : Plane) : ℝ :=
  singularStressY P gamma z.1 z.2 * phi z

theorem differentiableAt_fluxX_off_axis
    {P : Params} {gamma : ℝ → ℝ → ℝ} {w : Plane}
    (phi : SmoothTest ell)
    (hgamma : AnalyticAt ℝ (uncurried gamma) w)
    (hU : InU P w.1 w.2 (jetOf gamma w.1 w.2))
    (hy : w.2 ≠ 0) :
    DifferentiableAt ℝ (fluxX P gamma phi) w :=
  (differentiableAt_singularStressX_off_axis hgamma hU hy).mul
    (phi.differentiableAt w)

theorem differentiableAt_fluxY_off_axis
    {P : Params} {gamma : ℝ → ℝ → ℝ} {w : Plane}
    (phi : SmoothTest ell)
    (hgamma : AnalyticAt ℝ (uncurried gamma) w)
    (hU : InU P w.1 w.2 (jetOf gamma w.1 w.2))
    (hy : w.2 ≠ 0) :
    DifferentiableAt ℝ (fluxY P gamma phi) w :=
  (differentiableAt_singularStressY_off_axis hgamma hU hy).mul
    (phi.differentiableAt w)

theorem singularStressDivergence_eq_zero_on_localizedSquare
    {P : Params} {U : Set Plane} {r : ℝ}
    (K : CKOutcome P U r) (L : CompactSquareLocalization P K.gamma U)
    {w : Plane} (hw : w ∈ closedSquare L.ell) (hy : w.2 ≠ 0) :
    singularStressDivergence P K.gamma w.1 w.2 = 0 := by
  have hdomain : w ∈ U := L.closed_subset_domain hw
  have hbridge :=
    singularStressDivergence_eq_rpow_mul_residualNormal_of_inU
      hy (K.solution.1 w hdomain) (L.jet_inU w hw)
  have hsolve := K.solution.2.1 hdomain
  change residualNormal P w.2 (jetOf K.gamma w.1 w.2)
    (partialXX K.gamma w.1 w.2)
    (scalarDataField P K.gamma w.1 w.2) = 0 at hsolve
  rw [hbridge, hsolve, mul_zero]

theorem flux_divergence_eq_factoredPairing
    {P : Params} {U : Set Plane} {r : ℝ}
    (K : CKOutcome P U r) (L : CompactSquareLocalization P K.gamma U)
    (phi : SmoothTest L.ell) {w : Plane}
    (hw : w ∈ closedSquare L.ell) (hy : w.2 ≠ 0) :
    fderiv ℝ (fluxX P K.gamma phi) w (1, 0) +
        fderiv ℝ (fluxY P K.gamma phi) w (0, 1) =
      factoredPairing P K.gamma phi w := by
  have hgamma : AnalyticAt ℝ (uncurried K.gamma) w :=
    K.solution.1 w (L.closed_subset_domain hw)
  have hsx : DifferentiableAt ℝ
      (fun z : Plane => singularStressX P K.gamma z.1 z.2) w :=
    differentiableAt_singularStressX_off_axis hgamma (L.jet_inU w hw) hy
  have hsy : DifferentiableAt ℝ
      (fun z : Plane => singularStressY P K.gamma z.1 z.2) w :=
    differentiableAt_singularStressY_off_axis hgamma (L.jet_inU w hw) hy
  have hphi := phi.differentiableAt w
  have hfx : DifferentiableAt ℝ (fluxX P K.gamma phi) w :=
    hsx.mul hphi
  have hfy : DifferentiableAt ℝ (fluxY P K.gamma phi) w :=
    hsy.mul hphi
  rw [fderiv_prod_apply_eq_partialDerivs hfx,
    fderiv_prod_apply_eq_partialDerivs hfy]
  simp only [mul_one, mul_zero, add_zero, zero_add]
  have hsxPath : DifferentiableAt ℝ
      (fun x => singularStressX P K.gamma x w.2) w.1 := by
    exact hsx.comp w.1
      ((differentiableAt_id.prodMk (differentiableAt_const w.2)) :
        DifferentiableAt ℝ (fun x : ℝ => (x, w.2)) w.1)
  have hsyPath : DifferentiableAt ℝ
      (fun y => singularStressY P K.gamma w.1 y) w.2 := by
    have hpath : DifferentiableAt ℝ (fun y : ℝ => (w.1, y)) w.2 :=
      (differentiableAt_const w.1).prodMk differentiableAt_id
    convert DifferentiableAt.comp w.2 hsy hpath using 1 <;> rfl
  have hphiX : DifferentiableAt ℝ (fun x => phi (x, w.2)) w.1 := by
    exact hphi.comp w.1
      ((differentiableAt_id.prodMk (differentiableAt_const w.2)) :
        DifferentiableAt ℝ (fun x : ℝ => (x, w.2)) w.1)
  have hphiY : DifferentiableAt ℝ (fun y => phi (w.1, y)) w.2 := by
    exact hphi.comp w.2
      (((differentiableAt_const w.1).prodMk differentiableAt_id) :
        DifferentiableAt ℝ (fun y : ℝ => (w.1, y)) w.2)
  rw [show (fun x => fluxX P K.gamma phi (x, w.2)) =
      (fun x => singularStressX P K.gamma x w.2) *
        (fun x => phi (x, w.2)) by rfl,
    deriv_mul hsxPath hphiX,
    show (fun y => fluxY P K.gamma phi (w.1, y)) =
      (fun y => singularStressY P K.gamma w.1 y) *
        (fun y => phi (w.1, y)) by rfl,
    deriv_mul hsyPath hphiY]
  have hdiv := singularStressDivergence_eq_zero_on_localizedSquare K L hw hy
  simp only [singularStressDivergence] at hdiv
  dsimp only [factoredPairing]
  calc
    deriv (fun x => singularStressX P K.gamma x w.2) w.1 * phi (w.1, w.2) +
          singularStressX P K.gamma w.1 w.2 *
            deriv (fun x => phi (x, w.2)) w.1 +
        (deriv (fun y => singularStressY P K.gamma w.1 y) w.2 * phi (w.1, w.2) +
          singularStressY P K.gamma w.1 w.2 *
            deriv (fun y => phi (w.1, y)) w.2) =
        (deriv (fun x => singularStressX P K.gamma x w.2) w.1 +
          deriv (fun y => singularStressY P K.gamma w.1 y) w.2) * phi (w.1, w.2) +
          (singularStressX P K.gamma w.1 w.2 *
              deriv (fun x => phi (x, w.2)) w.1 +
            singularStressY P K.gamma w.1 w.2 *
              deriv (fun y => phi (w.1, y)) w.2) := by ring
    _ = singularStressX P K.gamma w.1 w.2 *
          deriv (fun x => phi (x, w.2)) w.1 +
        singularStressY P K.gamma w.1 w.2 *
          deriv (fun y => phi (w.1, y)) w.2 := by rw [hdiv, zero_mul, zero_add]

theorem closedSquare_of_mem_rectangle
    {ell a b : ℝ} (ha : -ell ≤ a) (hb : b ≤ ell)
    {w : Plane} (hw : w ∈ Icc (-ell, a) (ell, b)) :
    w ∈ closedSquare ell := by
  constructor
  · exact abs_le.mpr ⟨hw.1.1, hw.2.1⟩
  · exact abs_le.mpr ⟨ha.trans hw.1.2, hw.2.2.trans hb⟩

/-- Integration by parts on a closed rectangle which stays in one of the
two open half-planes.  The vertical side fluxes vanish because the test
function is supported in the open square. -/
theorem integral_factoredPairing_rectangle
    {P : Params} {U : Set Plane} {r a b : ℝ}
    (K : CKOutcome P U r) (L : CompactSquareLocalization P K.gamma U)
    (phi : SmoothTest L.ell)
    (ha : -L.ell ≤ a) (hab : a ≤ b) (hb : b ≤ L.ell)
    (hoff : ∀ y ∈ Icc a b, y ≠ 0) :
    (∫ z in Icc (-L.ell, a) (L.ell, b),
        factoredPairing P K.gamma phi z) =
      (∫ x in -L.ell..L.ell,
          singularStressY P K.gamma x b * phi (x, b)) -
        ∫ x in -L.ell..L.ell,
          singularStressY P K.gamma x a * phi (x, a) := by
  let R : Set Plane := Icc (-L.ell, a) (L.ell, b)
  have hell : -L.ell ≤ L.ell := by linarith [L.ell_pos]
  have hle : (-L.ell, a) ≤ (L.ell, b) := ⟨hell, hab⟩
  have hclosed : ∀ {w : Plane}, w ∈ R → w ∈ closedSquare L.ell := by
    intro w hw
    exact closedSquare_of_mem_rectangle ha hb hw
  have hoffR : ∀ {w : Plane}, w ∈ R → w.2 ≠ 0 := by
    intro w hw
    exact hoff w.2 ⟨hw.1.2, hw.2.2⟩
  have hcontX : ContinuousOn (fluxX P K.gamma phi) R := by
    intro w hw
    exact (differentiableAt_fluxX_off_axis phi
      (K.solution.1 w (L.closed_subset_domain (hclosed hw)))
      (L.jet_inU w (hclosed hw)) (hoffR hw)).continuousAt.continuousWithinAt
  have hcontY : ContinuousOn (fluxY P K.gamma phi) R := by
    intro w hw
    exact (differentiableAt_fluxY_off_axis phi
      (K.solution.1 w (L.closed_subset_domain (hclosed hw)))
      (L.jet_inU w (hclosed hw)) (hoffR hw)).continuousAt.continuousWithinAt
  have hdiffX : ∀ w ∈ Ioo (-L.ell) L.ell ×ˢ Ioo a b,
      HasFDerivAt (fluxX P K.gamma phi)
        (fderiv ℝ (fluxX P K.gamma phi) w) w := by
    intro w hw
    have hwR : w ∈ R := ⟨⟨hw.1.1.le, hw.2.1.le⟩,
      ⟨hw.1.2.le, hw.2.2.le⟩⟩
    exact (differentiableAt_fluxX_off_axis phi
      (K.solution.1 w (L.closed_subset_domain (hclosed hwR)))
      (L.jet_inU w (hclosed hwR)) (hoffR hwR)).hasFDerivAt
  have hdiffY : ∀ w ∈ Ioo (-L.ell) L.ell ×ˢ Ioo a b,
      HasFDerivAt (fluxY P K.gamma phi)
        (fderiv ℝ (fluxY P K.gamma phi) w) w := by
    intro w hw
    have hwR : w ∈ R := ⟨⟨hw.1.1.le, hw.2.1.le⟩,
      ⟨hw.1.2.le, hw.2.2.le⟩⟩
    exact (differentiableAt_fluxY_off_axis phi
      (K.solution.1 w (L.closed_subset_domain (hclosed hwR)))
      (L.jet_inU w (hclosed hwR)) (hoffR hwR)).hasFDerivAt
  have hpairCont : ContinuousOn (factoredPairing P K.gamma phi) R := by
    intro w hw
    have hwc := hclosed hw
    have hy := hoffR hw
    have hgamma := K.solution.1 w (L.closed_subset_domain hwc)
    have hU := L.jet_inU w hwc
    have hsx := (differentiableAt_singularStressX_off_axis hgamma hU hy).continuousAt
    have hsy := (differentiableAt_singularStressY_off_axis hgamma hU hy).continuousAt
    have hg : ContinuousAt (classicalGradient phi) w :=
      phi.continuous_gradient.continuousAt
    have hgcoords : ContinuousAt
        (fun z => (EuclideanSpace.equiv (Fin 2) ℝ) (classicalGradient phi z)) w :=
      (EuclideanSpace.equiv (Fin 2) ℝ).continuous.continuousAt.comp hg
    have hg0 : ContinuousAt
        (fun z : Plane => deriv (fun x => phi (x, z.2)) z.1) w := by
      simpa only [Function.comp_def, classicalGradient_apply_zero] using
        ((continuous_apply 0).continuousAt.comp hgcoords)
    have hg1 : ContinuousAt
        (fun z : Plane => deriv (fun y => phi (z.1, y)) z.2) w := by
      simpa only [Function.comp_def, classicalGradient_apply_one] using
        ((continuous_apply 1).continuousAt.comp hgcoords)
    exact ((hsx.mul hg0).add (hsy.mul hg1)).continuousWithinAt
  have hpairInt : IntegrableOn (factoredPairing P K.gamma phi) R :=
    hpairCont.integrableOn_compact isCompact_Icc
  have hdivInt : IntegrableOn
      (fun w => fderiv ℝ (fluxX P K.gamma phi) w (1, 0) +
        fderiv ℝ (fluxY P K.gamma phi) w (0, 1)) R := by
    apply hpairInt.congr_fun
    · intro w hw
      exact (flux_divergence_eq_factoredPairing K L phi (hclosed hw) (hoffR hw)).symm
    · exact measurableSet_Icc
  have hdiv := integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    (fluxX P K.gamma phi) (fluxY P K.gamma phi)
    (fderiv ℝ (fluxX P K.gamma phi))
    (fderiv ℝ (fluxY P K.gamma phi))
    (-L.ell, a) (L.ell, b) hle hcontX hcontY hdiffX hdiffY hdivInt
  have hleft : (fun y => fluxX P K.gamma phi (-L.ell, y)) = 0 := by
    funext y
    simp [fluxX, phi.eq_zero_left]
  have hright : (fun y => fluxX P K.gamma phi (L.ell, y)) = 0 := by
    funext y
    simp [fluxX, phi.eq_zero_right]
  have hleftInt : (∫ y in a..b, fluxX P K.gamma phi (-L.ell, y)) = 0 := by
    calc
      (∫ y in a..b, fluxX P K.gamma phi (-L.ell, y)) =
          ∫ _y in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro y _hy
        exact congrFun hleft y
      _ = 0 := intervalIntegral.integral_zero
  have hrightInt : (∫ y in a..b, fluxX P K.gamma phi (L.ell, y)) = 0 := by
    calc
      (∫ y in a..b, fluxX P K.gamma phi (L.ell, y)) =
          ∫ _y in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro y _hy
        exact congrFun hright y
      _ = 0 := intervalIntegral.integral_zero
  have heq : EqOn
      (fun w => fderiv ℝ (fluxX P K.gamma phi) w (1, 0) +
        fderiv ℝ (fluxY P K.gamma phi) w (0, 1))
      (factoredPairing P K.gamma phi) R := by
    intro w hw
    exact flux_divergence_eq_factoredPairing K L phi (hclosed hw) (hoffR hw)
  rw [setIntegral_congr_fun measurableSet_Icc heq] at hdiv
  rw [hleftInt, hrightInt] at hdiv
  simp only [sub_zero, add_zero] at hdiv
  simpa only [fluxY] using hdiv

/-! ## Exact excision of the central strip -/

/-- Up to the null horizontal cut lines and the null boundary of the square,
the cube is the disjoint union of the lower rectangle, central strip, and
upper rectangle.  This is the exact set-integral identity used below. -/
theorem cube_setIntegral_excision_split
    {ell delta : ℝ} (hdelta : 0 ≤ delta) (hdell : delta ≤ ell)
    (f : Plane → ℝ) (hf : Integrable f) :
    (∫ z in cube ell, f z) =
      ((∫ z in Icc (-ell, -ell) (ell, -delta), f z) +
        ∫ z in Icc (-ell, delta) (ell, ell), f z) +
        ∫ z in centralStrip ell delta, f z := by
  let lower : Set Plane := Ioo (-ell) ell ×ˢ Ioc (-ell) (-delta)
  let strip : Set Plane := Ioo (-ell) ell ×ˢ Ioc (-delta) delta
  let upper : Set Plane := Ioo (-ell) ell ×ˢ Ioc delta ell
  let whole : Set Plane := Ioo (-ell) ell ×ˢ Ioc (-ell) ell
  have hlower_meas : MeasurableSet lower := measurableSet_Ioo.prod measurableSet_Ioc
  have hstrip_meas : MeasurableSet strip := measurableSet_Ioo.prod measurableSet_Ioc
  have hupper_meas : MeasurableSet upper := measurableSet_Ioo.prod measurableSet_Ioc
  have hwhole : (lower ∪ strip) ∪ upper = whole := by
    ext z
    simp only [lower, strip, upper, whole, mem_union, mem_prod, mem_Ioo, mem_Ioc]
    constructor
    · rintro ((⟨hx, hy⟩ | ⟨hx, hy⟩) | ⟨hx, hy⟩)
      · exact ⟨hx, hy.1, hy.2.trans (neg_le_self hdelta) |>.trans hdell⟩
      · exact ⟨hx, (neg_le_neg hdell).trans_lt hy.1, hy.2.trans hdell⟩
      · exact ⟨hx, (neg_le_neg hdell).trans (neg_le_self hdelta) |>.trans_lt hy.1,
          hy.2⟩
    · rintro ⟨hx, hylo, hyhi⟩
      by_cases hlow : z.2 ≤ -delta
      · exact Or.inl (Or.inl ⟨hx, hylo, hlow⟩)
      · by_cases hmid : z.2 ≤ delta
        · exact Or.inl (Or.inr ⟨hx, lt_of_not_ge hlow, hmid⟩)
        · exact Or.inr ⟨hx, lt_of_not_ge hmid, hyhi⟩
  have hdisjLowerStrip : Disjoint lower strip := by
    rw [Set.disjoint_left]
    intro z hzLower hzStrip
    exact (not_lt_of_ge hzLower.2.2) hzStrip.2.1
  have hdisjUnionUpper : Disjoint (lower ∪ strip) upper := by
    rw [Set.disjoint_left]
    intro z hz hzUpper
    rcases hz with hzLower | hzStrip
    · exact (not_lt_of_ge (hzLower.2.2.trans (neg_le_self hdelta))) hzUpper.2.1
    · exact (not_lt_of_ge hzStrip.2.2) hzUpper.2.1
  have hcubeAE : cube ell =ᵐ[volume] whole := by
    rw [cube]
    simpa only [Measure.volume_eq_prod] using
      (Measure.set_prod_ae_eq (μ := volume) (ν := volume)
        (EventuallyEq.rfl) (Ioo_ae_eq_Ioc (μ := volume)))
  have hstripAE : centralStrip ell delta =ᵐ[volume] strip := by
    rw [centralStrip]
    simpa only [Measure.volume_eq_prod] using
      (Measure.set_prod_ae_eq (μ := volume) (ν := volume)
        (EventuallyEq.rfl) (Ioo_ae_eq_Ioc (μ := volume)))
  have hlowerAE : lower =ᵐ[volume] Icc (-ell, -ell) (ell, -delta) := by
    simpa only [lower, Icc_prod_eq, Measure.volume_eq_prod] using
      (Measure.set_prod_ae_eq (μ := volume) (ν := volume)
        (Ioo_ae_eq_Icc (μ := volume) (a := -ell) (b := ell))
        (Ioc_ae_eq_Icc (μ := volume) (a := -ell) (b := -delta)))
  have hupperAE : upper =ᵐ[volume] Icc (-ell, delta) (ell, ell) := by
    simpa only [upper, Icc_prod_eq, Measure.volume_eq_prod] using
      (Measure.set_prod_ae_eq (μ := volume) (ν := volume)
        (Ioo_ae_eq_Icc (μ := volume) (a := -ell) (b := ell))
        (Ioc_ae_eq_Icc (μ := volume) (a := delta) (b := ell)))
  have hlowerInt : IntegrableOn f lower := hf.integrableOn
  have hstripInt : IntegrableOn f strip := hf.integrableOn
  have hupperInt : IntegrableOn f upper := hf.integrableOn
  have hunionInt : IntegrableOn f (lower ∪ strip) :=
    hlowerInt.union hstripInt
  calc
    (∫ z in cube ell, f z) = ∫ z in whole, f z := setIntegral_congr_set hcubeAE
    _ = ∫ z in (lower ∪ strip) ∪ upper, f z := by rw [hwhole]
    _ = (∫ z in lower ∪ strip, f z) + ∫ z in upper, f z :=
      setIntegral_union hdisjUnionUpper hupper_meas hunionInt hupperInt
    _ = ((∫ z in lower, f z) + ∫ z in strip, f z) + ∫ z in upper, f z := by
      rw [setIntegral_union hdisjLowerStrip hstrip_meas hlowerInt hstripInt]
    _ = ((∫ z in Icc (-ell, -ell) (ell, -delta), f z) +
          ∫ z in Icc (-ell, delta) (ell, ell), f z) +
          ∫ z in centralStrip ell delta, f z := by
      rw [setIntegral_congr_set hlowerAE,
        setIntegral_congr_set hupperAE,
        setIntegral_congr_set hstripAE]
      ring

/-! ## Identification with the vector-valued stress -/

/-- The real Euclidean inner product in dimension two, written in the
coordinates fixed throughout the construction. -/
theorem inner_vector2_eq_coordinates (v w : Vector2) :
    inner ℝ v w =
      (EuclideanSpace.equiv (Fin 2) ℝ v) 0 *
          (EuclideanSpace.equiv (Fin 2) ℝ w) 0 +
        (EuclideanSpace.equiv (Fin 2) ℝ v) 1 *
          (EuclideanSpace.equiv (Fin 2) ℝ w) 1 := by
  rw [PiLp.inner_apply]
  simp [Fin.sum_univ_two, RCLike.inner_apply, mul_comm]

/-- The coordinate expression used in the excision calculation is exactly
the Euclidean pairing of the total stress representative with the classical
gradient.  The equality also holds on the light ray, since both chosen
representatives vanish there. -/
theorem inner_stressField_classicalGradient_eq_factoredPairing
    (P : Params) (gamma : ℝ → ℝ → ℝ) (phi : Plane → ℝ) (z : Plane) :
    inner ℝ (stressField P gamma z) (classicalGradient phi z) =
      factoredPairing P gamma phi z := by
  rcases z with ⟨x, y⟩
  by_cases hy : y = 0
  · subst y
    have hexponent : 2 / P.p ≠ 0 :=
      ne_of_gt (div_pos (by norm_num) P.p_pos)
    simp [factoredPairing, singularStressX, singularStressY,
      singularDenominator, hexponent]
  · rw [inner_vector2_eq_coordinates,
      stressField_coord_zero_off_axis P gamma x y hy,
      stressField_coord_one_off_axis P gamma x y hy,
      classicalGradient_apply_zero, classicalGradient_apply_one]
    rfl

/-- The weak-Euler pairing is integrable on the localized square.  This is
the only place where the full stress integrability estimate is used for a
smooth test. -/
theorem integrableOn_inner_stressField_classicalGradient
    {P : Params} {U : Set Plane} {r : ℝ}
    (K : CKOutcome P U r) (L : CompactSquareLocalization P K.gamma U)
    (phi : SmoothTest L.ell) :
    IntegrableOn
      (fun z => inner ℝ (stressField P K.gamma z)
        (classicalGradient phi z))
      (cube L.ell) volume := by
  let mu : Measure Plane := volume.restrict (cube L.ell)
  have hs : Integrable (stressField P K.gamma) mu := by
    change IntegrableOn (stressField P K.gamma) (cube L.ell) volume
    exact localized_stressField_integrableOn_cube L K.solution.1
  have hg : AEStronglyMeasurable (classicalGradient phi) mu := by
    exact phi.measurable_gradient.aestronglyMeasurable
  have hpair : AEStronglyMeasurable
      (fun z => inner ℝ (stressField P K.gamma z)
        (classicalGradient phi z)) mu :=
    hs.aestronglyMeasurable.inner hg
  obtain ⟨M, hMnonneg, hM⟩ :=
    phi.exists_gradient_norm_bound_on_closedSquare
  have hmajor : Integrable (fun z => M * ‖stressField P K.gamma z‖) mu :=
    hs.norm.const_mul M
  apply Integrable.mono' hmajor hpair
  filter_upwards [ae_restrict_mem (cube_measurable L.ell)] with z hz
  have hzclosed : z ∈ closedSquare L.ell :=
    ⟨abs_le.mpr ⟨hz.1.1.le, hz.1.2.le⟩,
      abs_le.mpr ⟨hz.2.1.le, hz.2.2.le⟩⟩
  calc
    ‖inner ℝ (stressField P K.gamma z) (classicalGradient phi z)‖ ≤
        ‖stressField P K.gamma z‖ * ‖classicalGradient phi z‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖stressField P K.gamma z‖ * M :=
      mul_le_mul_of_nonneg_left (hM z hzclosed) (norm_nonneg _)
    _ = M * ‖stressField P K.gamma z‖ := mul_comm _ _

/-- The scalar coordinate form used in the rectangle calculation is likewise
integrable on the square. -/
theorem integrableOn_factoredPairing
    {P : Params} {U : Set Plane} {r : ℝ}
    (K : CKOutcome P U r) (L : CompactSquareLocalization P K.gamma U)
    (phi : SmoothTest L.ell) :
    IntegrableOn (factoredPairing P K.gamma phi) (cube L.ell) volume := by
  have h := integrableOn_inner_stressField_classicalGradient K L phi
  apply h.congr_fun
  · intro z _hz
    exact inner_stressField_classicalGradient_eq_factoredPairing
      P K.gamma phi z
  · exact cube_measurable L.ell

/-- The global zero extension used in the shrinking-strip argument. -/
def localizedPairing (P : Params) (gamma : ℝ → ℝ → ℝ)
    {ell : ℝ} (phi : SmoothTest ell) : Plane → ℝ :=
  (cube ell).indicator (factoredPairing P gamma phi)

theorem integrable_localizedPairing
    {P : Params} {U : Set Plane} {r : ℝ}
    (K : CKOutcome P U r) (L : CompactSquareLocalization P K.gamma U)
    (phi : SmoothTest L.ell) :
    Integrable (localizedPairing P K.gamma phi) volume := by
  rw [localizedPairing, integrable_indicator_iff (cube_measurable L.ell)]
  exact integrableOn_factoredPairing K L phi

theorem setIntegral_localizedPairing_cube
    (P : Params) (gamma : ℝ → ℝ → ℝ)
    {ell : ℝ} (phi : SmoothTest ell) :
    (∫ z in cube ell, localizedPairing P gamma phi z) =
      ∫ z in cube ell, factoredPairing P gamma phi z := by
  apply setIntegral_congr_fun (cube_measurable ell)
  intro z hz
  simp [localizedPairing, hz]

theorem setIntegral_localizedPairing_rectangle
    (P : Params) (gamma : ℝ → ℝ → ℝ)
    {ell a b : ℝ} (phi : SmoothTest ell)
    (ha : -ell ≤ a) (hb : b ≤ ell) :
    (∫ z in Icc (-ell, a) (ell, b),
        localizedPairing P gamma phi z) =
      ∫ z in Icc (-ell, a) (ell, b),
        factoredPairing P gamma phi z := by
  let interior : Set Plane := Ioo (-ell) ell ×ˢ Ioo a b
  have hrectAE : Icc (-ell, a) (ell, b) =ᵐ[volume] interior := by
    simpa only [interior, Icc_prod_eq, Measure.volume_eq_prod] using
      (Measure.set_prod_ae_eq (μ := volume) (ν := volume)
        (Ioo_ae_eq_Icc (μ := volume) (a := -ell) (b := ell)).symm
        (Ioo_ae_eq_Icc (μ := volume) (a := a) (b := b)).symm)
  apply setIntegral_congr_ae measurableSet_Icc
  filter_upwards [hrectAE] with z hzAE hzRect
  have hzInterior : z ∈ interior := hzAE.mp hzRect
  have hzCube : z ∈ cube ell := by
    exact ⟨hzInterior.1,
      ⟨ha.trans_lt hzInterior.2.1, hzInterior.2.2.trans_le hb⟩⟩
  simp [localizedPairing, hzCube]

theorem setIntegral_localizedPairing_centralStrip
    (P : Params) (gamma : ℝ → ℝ → ℝ)
    {ell delta : ℝ} (phi : SmoothTest ell) (hdell : delta ≤ ell) :
    (∫ z in centralStrip ell delta,
        localizedPairing P gamma phi z) =
      ∫ z in centralStrip ell delta,
        factoredPairing P gamma phi z := by
  apply setIntegral_congr_fun
    (measurableSet_Ioo.prod measurableSet_Ioo)
  intro z hz
  have hzCube : z ∈ cube ell := by
    exact ⟨hz.1,
      ⟨(neg_le_neg hdell).trans_lt hz.2.1, hz.2.2.trans_le hdell⟩⟩
  simp [localizedPairing, hzCube]

/-! ## Quantitative control of the excision boundary -/

/-- The sum of the two horizontal boundary terms left by excising the strip
`|y| < delta`.  The signs agree with the outward normals of the lower and
upper rectangles. -/
def excisionOuter (P : Params) (gamma : ℝ → ℝ → ℝ)
    {ell : ℝ} (phi : SmoothTest ell) (delta : ℝ) : ℝ :=
  (∫ x in -ell..ell,
      singularStressY P gamma x (-delta) * phi (x, -delta)) -
    ∫ x in -ell..ell,
      singularStressY P gamma x delta * phi (x, delta)

/-- The quantitative normal-flux estimate.  Its exponent is positive because
`p > 2`, so this is precisely the removable-interface estimate. -/
theorem abs_excisionOuter_le
    {P : Params} {U : Set Plane} {r M delta : ℝ}
    (K : CKOutcome P U r) (L : CompactSquareLocalization P K.gamma U)
    (phi : SmoothTest L.ell)
    (hM : ∀ z ∈ closedSquare L.ell, |phi z| ≤ M)
    (hdelta : 0 < delta) (hdell : delta ≤ L.ell) :
    |excisionOuter P K.gamma phi delta| ≤
      (48 * L.ell * M) *
        delta ^ decayExponent P.p := by
  have hell : -L.ell ≤ L.ell := by linarith [L.ell_pos]
  have hlength : |L.ell - -L.ell| = 2 * L.ell := by
    rw [abs_of_pos]
    · ring
    · linarith [L.ell_pos]
  have hline (y : ℝ) (hyabs : |y| = delta) (hy0 : y ≠ 0) :
      ‖∫ x in -L.ell..L.ell,
          singularStressY P K.gamma x y * phi (x, y)‖ ≤
        (12 * M * delta ^ decayExponent P.p) *
          |L.ell - -L.ell| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le hell] at hx
    have hxclosed : |x| ≤ L.ell :=
      abs_le.mpr ⟨hx.1.le, hx.2⟩
    have hyclosed : |y| ≤ L.ell := by
      rw [hyabs]
      exact hdell
    have hzclosed : (x, y) ∈ closedSquare L.ell :=
      ⟨hxclosed, hyclosed⟩
    have hnormal : |singularStressY P K.gamma x y| ≤
        12 * delta ^ decayExponent P.p := by
      rw [← stressField_coord_one_off_axis P K.gamma x y hy0]
      change |normalStress P K.gamma x y| ≤ _
      calc
        |normalStress P K.gamma x y| ≤
            2 * 6 * |y| ^ decayExponent P.p :=
          abs_normalStress_le P K.gamma hy0
            (localized_factor_bounds L hzclosed).2
        _ = 12 * delta ^ decayExponent P.p := by
          rw [hyabs]
          ring
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |singularStressY P K.gamma x y| * |phi (x, y)| ≤
          (12 * delta ^ decayExponent P.p) * M :=
        mul_le_mul hnormal (hM (x, y) hzclosed) (abs_nonneg _)
          (by positivity)
      _ = 12 * M * delta ^ decayExponent P.p := by ring
  have hnegative := hline (-delta) (by rw [abs_neg, abs_of_pos hdelta])
    (neg_ne_zero.mpr hdelta.ne')
  have hpositive := hline delta (abs_of_pos hdelta) hdelta.ne'
  change
    |(∫ x in -L.ell..L.ell,
        singularStressY P K.gamma x (-delta) * phi (x, -delta)) -
      ∫ x in -L.ell..L.ell,
        singularStressY P K.gamma x delta * phi (x, delta)| ≤ _
  rw [← Real.norm_eq_abs]
  calc
    ‖(∫ x in -L.ell..L.ell,
        singularStressY P K.gamma x (-delta) * phi (x, -delta)) -
      ∫ x in -L.ell..L.ell,
        singularStressY P K.gamma x delta * phi (x, delta)‖ ≤
        ‖∫ x in -L.ell..L.ell,
          singularStressY P K.gamma x (-delta) * phi (x, -delta)‖ +
        ‖∫ x in -L.ell..L.ell,
          singularStressY P K.gamma x delta * phi (x, delta)‖ :=
      norm_sub_le _ _
    _ ≤ 2 * ((12 * M * delta ^ decayExponent P.p) *
          |L.ell - -L.ell|) := by
      linarith
    _ = (48 * L.ell * M) * delta ^ decayExponent P.p := by
      rw [hlength]
      ring

/-! ## The smooth weak Euler identity -/

/-- Exact integration by parts on the two excised rectangles, with the
central strip kept as the globally integrable zero extension. -/
theorem integral_factoredPairing_cube_eq_excision
    {P : Params} {U : Set Plane} {r delta : ℝ}
    (K : CKOutcome P U r) (L : CompactSquareLocalization P K.gamma U)
    (phi : SmoothTest L.ell)
    (hdelta : 0 < delta) (hdell : delta ≤ L.ell) :
    (∫ z in cube L.ell, factoredPairing P K.gamma phi z) =
      excisionOuter P K.gamma phi delta +
        ∫ z in centralStrip L.ell delta,
          localizedPairing P K.gamma phi z := by
  have hlowerBoundary :
      (∫ x in -L.ell..L.ell,
        singularStressY P K.gamma x (-L.ell) * phi (x, -L.ell)) = 0 := by
    calc
      (∫ x in -L.ell..L.ell,
        singularStressY P K.gamma x (-L.ell) * phi (x, -L.ell)) =
          ∫ _x in -L.ell..L.ell, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x _hx
        change singularStressY P K.gamma x (-L.ell) * phi (x, -L.ell) = 0
        rw [phi.eq_zero_bottom, mul_zero]
      _ = 0 := intervalIntegral.integral_zero
  have hupperBoundary :
      (∫ x in -L.ell..L.ell,
        singularStressY P K.gamma x L.ell * phi (x, L.ell)) = 0 := by
    calc
      (∫ x in -L.ell..L.ell,
        singularStressY P K.gamma x L.ell * phi (x, L.ell)) =
          ∫ _x in -L.ell..L.ell, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x _hx
        change singularStressY P K.gamma x L.ell * phi (x, L.ell) = 0
        rw [phi.eq_zero_top, mul_zero]
      _ = 0 := intervalIntegral.integral_zero
  have hlower := integral_factoredPairing_rectangle
    (a := -L.ell) (b := -delta) K L phi
    (le_refl _) (neg_le_neg hdell)
    (by linarith [L.ell_pos, hdelta]) (by
      intro y hy
      exact ne_of_lt (lt_of_le_of_lt hy.2 (neg_lt_zero.mpr hdelta)))
  have hupper := integral_factoredPairing_rectangle
    (a := delta) (b := L.ell) K L phi
    (by linarith [L.ell_pos, hdelta]) hdell (le_refl _) (by
      intro y hy
      exact ne_of_gt (hdelta.trans_le hy.1))
  rw [hlowerBoundary, sub_zero] at hlower
  rw [hupperBoundary, zero_sub] at hupper
  have hsplit := cube_setIntegral_excision_split
    hdelta.le hdell (localizedPairing P K.gamma phi)
      (integrable_localizedPairing K L phi)
  rw [setIntegral_localizedPairing_cube,
    setIntegral_localizedPairing_rectangle P K.gamma phi
      (a := -L.ell) (b := -delta) (le_refl _)
      (by linarith [L.ell_pos, hdelta]),
    setIntegral_localizedPairing_rectangle P K.gamma phi
      (a := delta) (b := L.ell)
      (by linarith [L.ell_pos, hdelta]) (le_refl _)] at hsplit
  rw [hlower, hupper] at hsplit
  dsimp only [excisionOuter]
  linarith

/-- Weak Euler equation for every `C¹` test compactly supported in the
localized square.  There are no auxiliary factor, Taylor-remainder, or
interface hypotheses: they are all consequences of `K` and `L`. -/
theorem smooth_weakEuler
    {P : Params} {U : Set Plane} {r : ℝ}
    (K : CKOutcome P U r) (L : CompactSquareLocalization P K.gamma U)
    (phi : SmoothTest L.ell) :
    (∫ z in cube L.ell,
      inner ℝ (stressField P K.gamma z) (classicalGradient phi z)) = 0 := by
  obtain ⟨M, hMnonneg, hM⟩ := phi.exists_abs_bound_on_closedSquare
  let f : Plane → ℝ := localizedPairing P K.gamma phi
  let outer : ℝ → ℝ := excisionOuter P K.gamma phi
  have hf : Integrable f volume := by
    simpa only [f] using integrable_localizedPairing K L phi
  have hpairing :
      (∫ z in cube L.ell,
        inner ℝ (stressField P K.gamma z) (classicalGradient phi z)) =
        ∫ z in cube L.ell, factoredPairing P K.gamma phi z := by
    apply setIntegral_congr_fun (cube_measurable L.ell)
    intro z _hz
    exact inner_stressField_classicalGradient_eq_factoredPairing
      P K.gamma phi z
  have hsmall : ∀ᶠ delta : ℝ in 𝓝[>] 0, delta ≤ L.ell := by
    have hlt : ∀ᶠ delta : ℝ in 𝓝 0, delta < L.ell :=
      eventually_lt_nhds L.ell_pos
    exact (hlt.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le
  have hsplit :
      (fun _ : ℝ =>
        ∫ z in cube L.ell,
          inner ℝ (stressField P K.gamma z) (classicalGradient phi z)) =ᶠ[𝓝[>] 0]
        fun delta => outer delta +
          ∫ z in centralStrip L.ell delta, f z := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with delta hdelta hdell
    change 0 < delta at hdelta
    rw [hpairing]
    exact integral_factoredPairing_cube_eq_excision
      K L phi hdelta hdell
  have houter : ∀ᶠ delta : ℝ in 𝓝[>] 0,
      |outer delta| ≤
        (48 * L.ell * M) * delta ^ decayExponent P.p := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with delta hdelta hdell
    change 0 < delta at hdelta
    exact abs_excisionOuter_le K L phi hM hdelta hdell
  exact weakEuler_of_excision P.two_lt_p L.ell_pos.le
    (mul_nonneg (mul_nonneg (by norm_num) L.ell_pos.le) hMnonneg)
    f hf outer hsplit houter

/-- Method-style spelling of `smooth_weakEuler`. -/
theorem CKOutcome.weakEuler_smooth
    {P : Params} {U : Set Plane} {r : ℝ}
    (K : CKOutcome P U r) (L : CompactSquareLocalization P K.gamma U)
    (phi : SmoothTest L.ell) :
    (∫ z in cube L.ell,
      inner ℝ (stressField P K.gamma z) (classicalGradient phi z)) = 0 :=
  smooth_weakEuler K L phi

end Theorem31
