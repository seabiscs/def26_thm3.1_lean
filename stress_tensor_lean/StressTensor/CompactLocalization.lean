import StressTensor.LocalizationBridge
import StressTensor.CauchyDataBridge
import StressTensor.AnalyticDifferentialBridge
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# Compact square localization after Cauchy--Kowalevskaya

This module formalizes the shrink-to-a-square step following (3.24).  The
value component of the jet is continuous automatically from analyticity.
Continuity of the four derivative components used by `jetOf` is first
isolated in `DerivativeJetContinuousAt` and then derived from analyticity.
-/

namespace StressTensor

noncomputable section

/-- The open square `(-ell,ell)^2`. -/
def openSquare (ell : ℝ) : Set Point :=
  {w | |w.1| < ell ∧ |w.2| < ell}

/-- The closed square `[-ell,ell]^2`. -/
def closedSquare (ell : ℝ) : Set Point :=
  {w | |w.1| ≤ ell ∧ |w.2| ≤ ell}

theorem isOpen_openSquare (ell : ℝ) : IsOpen (openSquare ell) := by
  have heq : openSquare ell = Metric.ball (0, 0) ell := by
    ext w
    simp [openSquare, Metric.mem_ball, Prod.dist_eq]
  rw [heq]
  exact Metric.isOpen_ball

theorem isClosed_closedSquare (ell : ℝ) : IsClosed (closedSquare ell) := by
  have heq : closedSquare ell = Metric.closedBall (0, 0) ell := by
    ext w
    simp [closedSquare, Metric.mem_closedBall, Prod.dist_eq]
  rw [heq]
  exact Metric.isClosed_closedBall

theorem isCompact_closedSquare (ell : ℝ) : IsCompact (closedSquare ell) := by
  have heq : closedSquare ell = Metric.closedBall (0, 0) ell := by
    ext w
    simp [closedSquare, Metric.mem_closedBall, Prod.dist_eq]
  rw [heq]
  exact ProperSpace.isCompact_closedBall (0, 0) ell

/-- For positive radius, the closed square is exactly the closure of the
open square. -/
theorem closure_openSquare {ell : ℝ} (hell : 0 < ell) :
    closure (openSquare ell) = closedSquare ell := by
  have hopen : openSquare ell = Metric.ball (0, 0) ell := by
    ext w
    simp [openSquare, Metric.mem_ball, Prod.dist_eq]
  have hclosed : closedSquare ell = Metric.closedBall (0, 0) ell := by
    ext w
    simp [closedSquare, Metric.mem_closedBall, Prod.dist_eq]
  rw [hopen, hclosed, closure_ball (0, 0) hell.ne']

@[simp] theorem origin_mem_openSquare {ell : ℝ} (hell : 0 < ell) :
    (0, 0) ∈ openSquare ell := by
  simpa [openSquare] using hell

@[simp] theorem origin_mem_closedSquare {ell : ℝ} (hell : 0 ≤ ell) :
    (0, 0) ∈ closedSquare ell := by
  simpa [closedSquare] using hell

/-- Every neighborhood of the origin contains a positive-radius closed
square. -/
theorem exists_closedSquare_subset_of_mem_nhds
    {W : Set Point} (hW : W ∈ nhds (0, 0)) :
    ∃ ell : ℝ, 0 < ell ∧ closedSquare ell ⊆ W := by
  rcases Metric.nhds_basis_ball.mem_iff.mp hW with ⟨eps, heps, hball⟩
  refine ⟨eps / 2, half_pos heps, ?_⟩
  intro w hw
  apply hball
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
  constructor
  · simpa only [Real.dist_eq, Prod.fst_zero, sub_zero] using
      lt_of_le_of_lt hw.1 (half_lt_self heps)
  · simpa only [Real.dist_eq, Prod.snd_zero, sub_zero] using
      lt_of_le_of_lt hw.2 (half_lt_self heps)

/-! ## Minimal continuity input for the actual jet -/

/-- Continuity at one point of the four derivative components in `jetOf`.
The value component is omitted: it follows directly from analyticity of
`uncurried gamma`. -/
structure DerivativeJetContinuousAt
    (gamma : ℝ → ℝ → ℝ) (w : Point) : Prop where
  dx : ContinuousAt (fun v : Point => (jetOf gamma v.1 v.2).dx) w
  dy : ContinuousAt (fun v : Point => (jetOf gamma v.1 v.2).dy) w
  dxy : ContinuousAt (fun v : Point => (jetOf gamma v.1 v.2).dxy) w
  dyy : ContinuousAt (fun v : Point => (jetOf gamma v.1 v.2).dyy) w

/-- Analyticity of the two-variable function supplies continuity of every
derivative component used by `jetOf`; hence the localization step needs no
extra regularity assumption for a CK solution. -/
theorem derivativeJetContinuousAt_of_analyticAt
    {gamma : ℝ → ℝ → ℝ} {w : Point}
    (hgamma : AnalyticAt ℝ (uncurried gamma) w) :
    DerivativeJetContinuousAt gamma w := by
  let f : Point → ℝ := uncurried gamma
  let vx : Point := (1, 0)
  let vy : Point := (0, 1)
  have hfder : AnalyticAt ℝ (fderiv ℝ f) w := by
    simpa only [f] using hgamma.fderiv
  have hFx : AnalyticAt ℝ (fun z => fderiv ℝ f z vx) w :=
    (hfder.contDiffAt.clm_apply contDiffAt_const).analyticAt
  have hFy : AnalyticAt ℝ (fun z => fderiv ℝ f z vy) w :=
    (hfder.contDiffAt.clm_apply contDiffAt_const).analyticAt
  have hsecond : AnalyticAt ℝ (fderiv ℝ (fderiv ℝ f)) w :=
    hfder.fderiv
  have hSecondY : AnalyticAt ℝ
      (fun z => fderiv ℝ (fderiv ℝ f) z vy) w :=
    (hsecond.contDiffAt.clm_apply contDiffAt_const).analyticAt
  have hSecondYX : AnalyticAt ℝ
      (fun z => fderiv ℝ (fderiv ℝ f) z vy vx) w :=
    (hSecondY.contDiffAt.clm_apply contDiffAt_const).analyticAt
  have hSecondYY : AnalyticAt ℝ
      (fun z => fderiv ℝ (fderiv ℝ f) z vy vy) w :=
    (hSecondY.contDiffAt.clm_apply contDiffAt_const).analyticAt
  have hev : ∀ᶠ z in nhds w, AnalyticAt ℝ f z := by
    simpa only [f] using hgamma.eventually_analyticAt
  have heqDx :
      (fun z : Point => (jetOf gamma z.1 z.2).dx) =ᶠ[nhds w]
        (fun z => fderiv ℝ f z vx) := by
    filter_upwards [hev] with z hz
    simpa only [jetOf, f, vx] using
      partialX_eq_fderiv_uncurried hz.differentiableAt
  have heqDy :
      (fun z : Point => (jetOf gamma z.1 z.2).dy) =ᶠ[nhds w]
        (fun z => fderiv ℝ f z vy) := by
    filter_upwards [hev] with z hz
    simpa only [jetOf, f, vy] using
      partialY_eq_fderiv_uncurried hz.differentiableAt
  have heqDxy :
      (fun z : Point => (jetOf gamma z.1 z.2).dxy) =ᶠ[nhds w]
        (fun z => fderiv ℝ (fderiv ℝ f) z vy vx) := by
    filter_upwards [hev] with z hz
    simpa only [jetOf, f, vx, vy] using
      partialXY_eq_secondFDeriv_uncurried hz
  have heqDyy :
      (fun z : Point => (jetOf gamma z.1 z.2).dyy) =ᶠ[nhds w]
        (fun z => fderiv ℝ (fderiv ℝ f) z vy vy) := by
    filter_upwards [hev] with z hz
    simpa only [jetOf, f, vy] using
      partialYY_eq_secondFDeriv_uncurried hz
  exact ⟨hFx.continuousAt.congr_of_eventuallyEq heqDx,
    hFy.continuousAt.congr_of_eventuallyEq heqDy,
    hSecondYX.continuousAt.congr_of_eventuallyEq heqDxy,
    hSecondYY.continuousAt.congr_of_eventuallyEq heqDyy⟩

/-- Analyticity of the value together with continuity of the four derivative
components makes membership of the actual jet in `U_q` hold eventually near
the origin.  The Cauchy data identify the center jet exactly. -/
theorem eventually_inU_jetOf_origin
    (P : Params) {gamma : ℝ → ℝ → ℝ} {r : ℝ}
    (hdata : HasCauchyDataOn gamma r) (hr : 0 < r)
    (hanalytic : AnalyticAt ℝ (uncurried gamma) (0, 0))
    (hjetCont : DerivativeJetContinuousAt gamma (0, 0)) :
    {w : Point | InU P w.1 w.2 (jetOf gamma w.1 w.2)} ∈ nhds (0, 0) := by
  have hzero : |(0 : ℝ)| < r := by simpa using hr
  have hjet0 : jetOf gamma 0 0 = initialJet :=
    jetOf_zero_eq_initialJet_of_cauchyData hdata hzero
  have hU0 : InU P 0 0 (jetOf gamma 0 0) := by
    rw [hjet0]
    exact initialJet_inU P (by simpa using P.rho_pos)
  have hxCont : ContinuousAt (fun w : Point => |w.1|) (0, 0) :=
    continuousAt_fst.abs
  have hyCont : ContinuousAt (fun w : Point => |w.2|) (0, 0) :=
    continuousAt_snd.abs
  have hvalCont :
      ContinuousAt (fun w : Point => |(jetOf gamma w.1 w.2).val|) (0, 0) := by
    simpa only [jetOf, uncurried] using hanalytic.continuousAt.abs
  have hdxCont : ContinuousAt
      (fun w : Point => |(jetOf gamma w.1 w.2).dx + 1|) (0, 0) :=
    (hjetCont.dx.add continuousAt_const).abs
  have hdyCont : ContinuousAt
      (fun w : Point => |(jetOf gamma w.1 w.2).dy|) (0, 0) :=
    hjetCont.dy.abs
  have hdxyCont : ContinuousAt
      (fun w : Point => |(jetOf gamma w.1 w.2).dxy|) (0, 0) :=
    hjetCont.dxy.abs
  have hdyyCont : ContinuousAt
      (fun w : Point => |(jetOf gamma w.1 w.2).dyy|) (0, 0) :=
    hjetCont.dyy.abs
  have hxEv := hxCont.eventually_lt continuousAt_const hU0.1.1
  have hyEv := hyCont.eventually_lt continuousAt_const hU0.1.2
  have hvalEv := hvalCont.eventually_lt continuousAt_const hU0.2.1
  have hdxEv := hdxCont.eventually_lt continuousAt_const hU0.2.2.1
  have hdyEv := hdyCont.eventually_lt continuousAt_const hU0.2.2.2.1
  have hdxyEv := hdxyCont.eventually_lt continuousAt_const hU0.2.2.2.2.1
  have hdyyEv := hdyyCont.eventually_lt continuousAt_const hU0.2.2.2.2.2
  filter_upwards [hxEv, hyEv, hvalEv, hdxEv, hdyEv, hdxyEv, hdyyEv]
    with w hx hy hval hdx hdy hdxy hdyy
  exact ⟨⟨hx, hy⟩, hval, hdx, hdy, hdxy, hdyy⟩

/-! ## The compact localized square -/

/-- Data produced by shrinking an analytic CK neighborhood to a closed
centered square on which the actual jet remains in `U_q`. -/
structure CompactSquareLocalization
    (P : Params) (gamma : ℝ → ℝ → ℝ) (U : Set Point) where
  ell : ℝ
  ell_pos : 0 < ell
  closed_subset_domain : closedSquare ell ⊆ U
  jet_inU : ∀ w ∈ closedSquare ell,
    InU P w.1 w.2 (jetOf gamma w.1 w.2)

/-- The precise shrink-to-a-square conclusion after CK. -/
theorem CKOutcome.exists_compactSquareLocalization
    {P : Params} {U : Set Point} {r : ℝ} (K : CKOutcome P U r)
    (hjetCont : DerivativeJetContinuousAt K.gamma (0, 0)) :
    Nonempty (CompactSquareLocalization P K.gamma U) := by
  have hdomain : U ∈ nhds (0, 0) :=
    K.isOpen_domain.mem_nhds K.origin_mem
  have hlocal :
      {w : Point | InU P w.1 w.2 (jetOf K.gamma w.1 w.2)} ∈ nhds (0, 0) :=
    eventually_inU_jetOf_origin P K.solution.2.2 K.radius_pos
      (K.solution.1 (0, 0) K.origin_mem) hjetCont
  have htarget :
      U ∩ {w : Point | InU P w.1 w.2 (jetOf K.gamma w.1 w.2)} ∈
        nhds (0, 0) := Filter.inter_mem hdomain hlocal
  rcases exists_closedSquare_subset_of_mem_nhds htarget with
    ⟨ell, hell, hsub⟩
  refine ⟨⟨ell, hell, ?_, ?_⟩⟩
  · intro w hw
    exact (hsub hw).1
  · rintro ⟨x, y⟩ hxy
    exact (hsub hxy).2

/-- Fully discharged shrink-to-a-square conclusion for a CK outcome. -/
theorem CKOutcome.exists_compactSquareLocalization_of_analytic
    {P : Params} {U : Set Point} {r : ℝ} (K : CKOutcome P U r) :
    Nonempty (CompactSquareLocalization P K.gamma U) := by
  exact K.exists_compactSquareLocalization
    (derivativeJetContinuousAt_of_analyticAt
      (K.solution.1 (0, 0) K.origin_mem))

/-! ## Uniform consequences on the localized square -/

/-- Analyticity of the uncurried function supplies differentiability of
both coordinate slices. -/
theorem differentiableAt_coordinateSlices_of_analyticAt
    {gamma : ℝ → ℝ → ℝ} {x y : ℝ}
    (hgamma : AnalyticAt ℝ (uncurried gamma) (x, y)) :
    DifferentiableAt ℝ (fun xi => gamma xi y) x ∧
      DifferentiableAt ℝ (gamma x) y := by
  have hxAnalytic : AnalyticAt ℝ (fun xi : ℝ => gamma xi y) x := by
    simpa [uncurried] using
      hgamma.comp₂ (analyticAt_id : AnalyticAt ℝ (fun xi : ℝ => xi) x)
        (analyticAt_const : AnalyticAt ℝ (fun _xi : ℝ => y) x)
  have hyAnalytic : AnalyticAt ℝ (gamma x) y := by
    simpa [uncurried] using
      hgamma.comp₂ (analyticAt_const : AnalyticAt ℝ (fun _eta : ℝ => x) y)
        (analyticAt_id : AnalyticAt ℝ (fun eta : ℝ => eta) y)
  exact ⟨hxAnalytic.differentiableAt, hyAnalytic.differentiableAt⟩

namespace CompactSquareLocalization

variable {P : Params} {gamma : ℝ → ℝ → ℝ} {U : Set Point}
    (L : CompactSquareLocalization P gamma U)

theorem isCompact : IsCompact (closedSquare L.ell) :=
  isCompact_closedSquare L.ell

/-- The associated open square is also contained in the CK domain. -/
theorem open_subset_domain : openSquare L.ell ⊆ U := by
  intro w hw
  apply L.closed_subset_domain
  exact ⟨hw.1.le, hw.2.le⟩

/-- The open square is relatively compact in the CK domain in the concrete
sense used by the manuscript: its compact closure is contained in `U`. -/
theorem closure_open_subset_domain : closure (openSquare L.ell) ⊆ U := by
  rw [closure_openSquare L.ell_pos]
  exact L.closed_subset_domain

/-- Uniform two-sided bounds for the composed deficit factor. -/
theorem Ccomp_bounds {w : Point} (hw : w ∈ closedSquare L.ell) :
    (1 : ℝ) / 4 < Ccomp P w.2 (jetOf gamma w.1 w.2) ∧
      Ccomp P w.2 (jetOf gamma w.1 w.2) < 4 := by
  exact Ccomp_bounds_of_inU (L.jet_inU w hw)

/-- `Gamma0` is uniformly below `-1` on the entire closed square. -/
theorem gamma0_lt_neg_one {w : Point} (hw : w ∈ closedSquare L.ell) :
    gamma0 w.2 (jetOf gamma w.1 w.2) < -1 := by
  exact gamma0_lt_neg_one_of_inU (L.jet_inU w hw)

/-- The leading CK coefficient has its uniform quantitative lower bound on
the closed square. -/
theorem coeff0_ge {w : Point} (hw : w ∈ closedSquare L.ell) :
    (P.q - 1) / 1024 ≤
      coeff0 w.2 (jetOf gamma w.1 w.2)
        (scalarDataOfJet P w.2 (jetOf gamma w.1 w.2)) := by
  exact coeff0_scalarDataOfJet_ge_of_inU P (L.jet_inU w hw)

/-- The actual ansatz gradient is exactly `(1,0)` on the portion of the
axis inside the square. -/
theorem actualAnsatzGradient_axis
    (hanalytic : AnalyticOnNhd ℝ (uncurried gamma) U)
    {x : ℝ} (hx : (x, 0) ∈ closedSquare L.ell) :
    actualAnsatzGradient gamma x 0 = (1, 0) := by
  have hdiff := differentiableAt_coordinateSlices_of_analyticAt
    (hanalytic (x, 0) (L.closed_subset_domain hx))
  exact StressTensor.actualAnsatzGradient_on_axis hdiff.1 hdiff.2

/-- The actual gradient has squared norm one on the localized light axis. -/
theorem normSq_actualAnsatzGradient_axis
    (hanalytic : AnalyticOnNhd ℝ (uncurried gamma) U)
    {x : ℝ} (hx : (x, 0) ∈ closedSquare L.ell) :
    normSq (actualAnsatzGradient gamma x 0) = 1 := by
  rw [L.actualAnsatzGradient_axis hanalytic hx]
  norm_num [normSq]

/-- At every off-axis point of the square, the actual gradient is strictly
spacelike. -/
theorem normSq_actualAnsatzGradient_lt_one
    (hanalytic : AnalyticOnNhd ℝ (uncurried gamma) U)
    {w : Point} (hw : w ∈ closedSquare L.ell) (hy0 : w.2 ≠ 0) :
    normSq (actualAnsatzGradient gamma w.1 w.2) < 1 := by
  have hdiff := differentiableAt_coordinateSlices_of_analyticAt
    (hanalytic w (L.closed_subset_domain hw))
  exact normSq_actualAnsatzGradient_lt_one_of_inU
    (L.jet_inU w hw) hy0 hdiff.1 hdiff.2

/-- On the localized open square, an analytic solution of the auxiliary
equation makes the original energy-gradient stress divergence-free at every
off-axis point.  This combines the actual/factored stress identification with
the fully discharged differential bridge. -/
theorem energyGradientStressDivergence_eq_zero_off_axis
    (hanalytic : AnalyticOnNhd ℝ (uncurried gamma) U)
    (hsolve : SolvesAuxiliaryOn P U gamma)
    {w : Point} (hw : w ∈ openSquare L.ell) (hy0 : w.2 ≠ 0) :
    energyGradientStressDivergence P gamma w.1 w.2 = 0 := by
  let W : Set Point := openSquare L.ell ∩ {z : Point | z.2 ≠ 0}
  have hWopen : IsOpen W := by
    apply (isOpen_openSquare L.ell).inter
    exact (isOpen_ne : IsOpen {y : ℝ | y ≠ 0}).preimage continuous_snd
  have hwW : w ∈ W := ⟨hw, hy0⟩
  have hadm : ∀ z : Point, z ∈ W →
      StressFactorizationAdmissibleAt P gamma z.1 z.2 := by
    intro z hz
    have hzClosed : z ∈ closedSquare L.ell := ⟨hz.1.1.le, hz.1.2.le⟩
    have hzDomain : z ∈ U := L.closed_subset_domain hzClosed
    have hdiff := differentiableAt_coordinateSlices_of_analyticAt
      (hanalytic z hzDomain)
    exact stressFactorizationAdmissibleAt_of_inU
      (L.jet_inU z hzClosed) hz.2 hdiff.1 hdiff.2
  have horiginal :=
    energyGradientStressDivergence_eq_singularStressDivergence_of_isOpen
      hWopen hwW hadm
  have hwClosed : w ∈ closedSquare L.ell := ⟨hw.1.le, hw.2.le⟩
  have hwDomain : w ∈ U := L.closed_subset_domain hwClosed
  have hsingular :=
    singularStressDivergence_eq_rpow_mul_residualNormal_of_inU
      hy0 (hanalytic w hwDomain) (L.jet_inU w hwClosed)
  have hres := hsolve hwDomain
  change residualNormal P w.2 (jetOf gamma w.1 w.2)
    (partialXX gamma w.1 w.2) (scalarDataField P gamma w.1 w.2) = 0 at hres
  calc
    energyGradientStressDivergence P gamma w.1 w.2 =
        singularStressDivergence P gamma w.1 w.2 := horiginal
    _ = Real.rpow |w.2| (-(2 / P.p)) *
        residualNormal P w.2 (jetOf gamma w.1 w.2)
          (partialXX gamma w.1 w.2) (scalarDataField P gamma w.1 w.2) := hsingular
    _ = 0 := by rw [hres, mul_zero]

end CompactSquareLocalization

end

end StressTensor
