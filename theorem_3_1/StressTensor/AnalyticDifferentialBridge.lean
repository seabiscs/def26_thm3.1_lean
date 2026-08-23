import StressTensor.ScalarNeighborhood
import StressTensor.DifferentialBridge
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Analytic discharge of the scalar differential hypotheses

`DifferentialBridge` deliberately accepts the full Fréchet derivative of
`S̃` as an explicit hypothesis.  The local analyticity established in
`ScalarAnalyticity` supplies that derivative near `(0,-2)`.  This file proves
that its two coordinates are exactly the one-variable derivatives stored in
`ScalarData`, and consequently discharges the scalar hypothesis in the chain,
product, residual, and off-axis divergence formulas.

Regularity of the separate function `γ` is explicit in the low-level bridge;
the strongest theorems in this file discharge it from `AnalyticAt ℝ
(uncurried γ)`.
-/

namespace StressTensor

noncomputable section

open scoped ContDiff

/-! ## Coordinate differentials of the scalar factors -/

/-- `C̃` regarded as a function on its two-dimensional scalar domain. -/
def ctildeUncurried (P : Params) : ℝ × ℝ → ℝ :=
  fun w => Ctilde P w.1 w.2

/-- The full coordinate differential of `C̃`, expressed using its two
one-variable derivatives. -/
def ctildeDifferential (P : Params) (t d : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  deriv (fun τ => Ctilde P τ d) t • ContinuousLinearMap.fst ℝ ℝ ℝ +
    deriv (Ctilde P t) d • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem ctildeDifferential_apply
    (P : Params) (t d : ℝ) (v : ℝ × ℝ) :
    ctildeDifferential P t d v =
      deriv (fun τ => Ctilde P τ d) t * v.1 +
        deriv (Ctilde P t) d * v.2 := by
  simp [ctildeDifferential]

/-- For a differentiable scalar function of two real variables, its Fréchet
derivative is determined by the two ordinary coordinate derivatives. -/
private theorem hasFDerivAt_eq_coordinateDifferential
    {f : ℝ × ℝ → ℝ} {t d : ℝ}
    (h : DifferentiableAt ℝ f (t, d)) :
    HasFDerivAt f
      (deriv (fun τ => f (τ, d)) t • ContinuousLinearMap.fst ℝ ℝ ℝ +
        deriv (fun δ => f (t, δ)) d • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (t, d) := by
  let D : (ℝ × ℝ) →L[ℝ] ℝ := fderiv ℝ f (t, d)
  have hraw : HasFDerivAt f D (t, d) := by
    simpa only [D] using h.hasFDerivAt
  have htPath : HasDerivAt (fun τ : ℝ => (τ, d)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t d)
  have hdPath : HasDerivAt (fun δ : ℝ => (t, δ)) (0, 1) d :=
    (hasDerivAt_const d t).prodMk (hasDerivAt_id d)
  have htComp : HasDerivAt (fun τ => f (τ, d)) (D (1, 0)) t :=
    hraw.comp_hasDerivAt t htPath
  have hdComp : HasDerivAt (fun δ => f (t, δ)) (D (0, 1)) d :=
    hraw.comp_hasDerivAt d hdPath
  apply hraw.congr_fderiv
  apply ContinuousLinearMap.ext
  rintro ⟨a, b⟩
  have hv : (a, b) = a • ((1, 0) : ℝ × ℝ) + b • (0, 1) := by
    ext <;> simp
  rw [hv, map_add, map_smul, map_smul, htComp.deriv, hdComp.deriv]
  simp
  ring

/-- Differentiability of `C̃` gives its full derivative in coordinate form. -/
theorem hasFDerivAt_ctildeUncurried_of_differentiableAt
    {P : Params} {t d : ℝ}
    (h : DifferentiableAt ℝ (ctildeUncurried P) (t, d)) :
    HasFDerivAt (ctildeUncurried P) (ctildeDifferential P t d) (t, d) := by
  simpa only [ctildeUncurried, ctildeDifferential] using
    hasFDerivAt_eq_coordinateDifferential h

/-- Differentiability of `S̃` gives exactly the differential encoded by
`scalarDataAt`. -/
theorem hasFDerivAt_stildeUncurried_of_differentiableAt
    {P : Params} {t d : ℝ}
    (h : DifferentiableAt ℝ (stildeUncurried P) (t, d)) :
    HasFDerivAt (stildeUncurried P)
      (scalarDifferential (scalarDataAt P t d)) (t, d) := by
  simpa only [stildeUncurried, scalarDifferential, scalarDataAt] using
    hasFDerivAt_eq_coordinateDifferential h

/-! ## A common analytic neighborhood of `(0,-2)` -/

/-- The maximal open region on which both continued scalar factors are
analytic.  `ScalarAnalyticity` proves that it contains `(0,-2)`. -/
def scalarAnalyticRegion (P : Params) : Set (ℝ × ℝ) :=
  {w | AnalyticAt ℝ (ctildeUncurried P) w ∧
    AnalyticAt ℝ (stildeUncurried P) w}

theorem isOpen_scalarAnalyticRegion (P : Params) :
    IsOpen (scalarAnalyticRegion P) := by
  exact (isOpen_analyticAt ℝ (ctildeUncurried P)).inter
    (isOpen_analyticAt ℝ (stildeUncurried P))

theorem origin_mem_scalarAnalyticRegion (P : Params) :
    ((0, -2) : ℝ × ℝ) ∈ scalarAnalyticRegion P := by
  constructor
  · change AnalyticAt ℝ (fun z : ℝ × ℝ => Ctilde P z.1 z.2) (0, -2)
    exact analyticAt_Ctilde_origin P
  · change AnalyticAt ℝ (fun z : ℝ × ℝ => Stilde P z.1 z.2) (0, -2)
    exact analyticAt_Stilde_origin P

/-- The explicit scalar neighborhood `V_q` lies in the common analytic
region. -/
theorem inV_mem_scalarAnalyticRegion
    {P : Params} {t d : ℝ} (h : InV P t d) :
    (t, d) ∈ scalarAnalyticRegion P := by
  exact ⟨h.analyticAt_Ctilde, h.analyticAt_Stilde⟩

/-- Membership of a jet in `U_q` automatically places its composed scalar
point in the common analytic region. -/
theorem scalarPoint_mem_scalarAnalyticRegion_of_inU
    {P : Params} {x y : ℝ} {z : Jet} (h : InU P x y z) :
    (y, gamma0 y z) ∈ scalarAnalyticRegion P :=
  inV_mem_scalarAnalyticRegion (inV_gamma0_of_inU h)

theorem scalarAnalyticRegion_mem_nhds_origin (P : Params) :
    scalarAnalyticRegion P ∈ nhds ((0, -2) : ℝ × ℝ) :=
  (isOpen_scalarAnalyticRegion P).mem_nhds (origin_mem_scalarAnalyticRegion P)

theorem analyticOnNhd_ctilde_scalarAnalyticRegion (P : Params) :
    AnalyticOnNhd ℝ (ctildeUncurried P) (scalarAnalyticRegion P) :=
  fun _w hw => hw.1

theorem analyticOnNhd_stilde_scalarAnalyticRegion (P : Params) :
    AnalyticOnNhd ℝ (stildeUncurried P) (scalarAnalyticRegion P) :=
  fun _w hw => hw.2

theorem analyticAt_ctildeUncurried_of_mem
    {P : Params} {w : ℝ × ℝ} (h : w ∈ scalarAnalyticRegion P) :
    AnalyticAt ℝ (ctildeUncurried P) w :=
  h.1

theorem analyticAt_stildeUncurried_of_mem
    {P : Params} {w : ℝ × ℝ} (h : w ∈ scalarAnalyticRegion P) :
    AnalyticAt ℝ (stildeUncurried P) w :=
  h.2

theorem hasFDerivAt_ctildeUncurried_of_mem
    {P : Params} {t d : ℝ} (h : (t, d) ∈ scalarAnalyticRegion P) :
    HasFDerivAt (ctildeUncurried P) (ctildeDifferential P t d) (t, d) :=
  hasFDerivAt_ctildeUncurried_of_differentiableAt h.1.differentiableAt

theorem hasFDerivAt_stildeUncurried_of_mem
    {P : Params} {t d : ℝ} (h : (t, d) ∈ scalarAnalyticRegion P) :
    HasFDerivAt (stildeUncurried P)
      (scalarDifferential (scalarDataAt P t d)) (t, d) :=
  hasFDerivAt_stildeUncurried_of_differentiableAt h.2.differentiableAt

/-- The first coordinate partial of `Stilde`, as a function of both scalar
variables, is analytic throughout the common analytic region. -/
theorem analyticAt_stildePartialT_of_mem
    {P : Params} {w : ℝ × ℝ} (h : w ∈ scalarAnalyticRegion P) :
    AnalyticAt ℝ
      (fun z : ℝ × ℝ => deriv (fun t => Stilde P t z.2) z.1) w := by
  have hFder : AnalyticAt ℝ (fderiv ℝ (stildeUncurried P)) w := h.2.fderiv
  have hEval : AnalyticAt ℝ
      (fun z => fderiv ℝ (stildeUncurried P) z (1, 0)) w :=
    (hFder.contDiffAt.clm_apply contDiffAt_const).analyticAt
  have hev : ∀ᶠ z in nhds w, AnalyticAt ℝ (stildeUncurried P) z :=
    h.2.eventually_analyticAt
  apply hEval.congr
  filter_upwards [hev] with z hz
  have hfull := hasFDerivAt_stildeUncurried_of_differentiableAt hz.differentiableAt
  have heq := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1, 0)) hfull.fderiv
  simpa only [scalarDifferential_apply, scalarDataAt, mul_one, mul_zero, add_zero]
    using heq

/-- The second coordinate partial of `Stilde`, as a function of both scalar
variables, is analytic throughout the common analytic region. -/
theorem analyticAt_stildePartialD_of_mem
    {P : Params} {w : ℝ × ℝ} (h : w ∈ scalarAnalyticRegion P) :
    AnalyticAt ℝ
      (fun z : ℝ × ℝ => deriv (Stilde P z.1) z.2) w := by
  have hFder : AnalyticAt ℝ (fderiv ℝ (stildeUncurried P)) w := h.2.fderiv
  have hEval : AnalyticAt ℝ
      (fun z => fderiv ℝ (stildeUncurried P) z (0, 1)) w :=
    (hFder.contDiffAt.clm_apply contDiffAt_const).analyticAt
  have hev : ∀ᶠ z in nhds w, AnalyticAt ℝ (stildeUncurried P) z :=
    h.2.eventually_analyticAt
  apply hEval.congr
  filter_upwards [hev] with z hz
  have hfull := hasFDerivAt_stildeUncurried_of_differentiableAt hz.differentiableAt
  have heq := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1)) hfull.fderiv
  simpa only [scalarDifferential_apply, scalarDataAt, mul_zero, mul_one, zero_add]
    using heq

theorem hasFDerivAt_ctildeUncurried_origin (P : Params) :
    HasFDerivAt (ctildeUncurried P) (ctildeDifferential P 0 (-2)) (0, -2) :=
  hasFDerivAt_ctildeUncurried_of_mem (origin_mem_scalarAnalyticRegion P)

theorem hasFDerivAt_stildeUncurried_origin (P : Params) :
    HasFDerivAt (stildeUncurried P)
      (scalarDifferential (scalarDataAt P 0 (-2))) (0, -2) :=
  hasFDerivAt_stildeUncurried_of_mem (origin_mem_scalarAnalyticRegion P)

/-- Membership of the composed scalar point discharges exactly the full
`S̃`-differential hypothesis used throughout `DifferentialBridge`. -/
theorem hasFDerivAt_stildeUncurried_scalarDataField_of_mem
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (h : (y, gamma0Field γ x y) ∈ scalarAnalyticRegion P) :
    HasFDerivAt (stildeUncurried P)
      (scalarDifferential (scalarDataField P γ x y))
      (y, gamma0Field γ x y) := by
  exact hasFDerivAt_stildeUncurried_of_mem h

/-! ## The derivative hypotheses supplied by analyticity of `γ` -/

/-- The six first- and second-order one-variable derivative statements used
by `DifferentialBridge`, packaged together.  The mixed `x`-then-`y` value is
used in both orders. -/
structure GammaDifferentialDataAt
    (γ : ℝ → ℝ → ℝ) (x y : ℝ) : Prop where
  dx : HasDerivAt (fun ξ => γ ξ y) (partialX γ x y) x
  dxx : HasDerivAt (fun ξ => partialX γ ξ y) (partialXX γ x y) x
  dyx : HasDerivAt (fun ξ => partialY γ ξ y) (partialXY γ x y) x
  dy : HasDerivAt (γ x) (partialY γ x y) y
  dxy : HasDerivAt (fun η => partialX γ x η) (partialXY γ x y) y
  dyy : HasDerivAt (fun η => partialY γ x η) (partialYY γ x y) y

theorem partialX_eq_fderiv_uncurried
    {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (h : DifferentiableAt ℝ (uncurried γ) (x, y)) :
    partialX γ x y = fderiv ℝ (uncurried γ) (x, y) (1, 0) := by
  have hpath : HasDerivAt (fun ξ : ℝ => (ξ, y)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have hcomp := h.hasFDerivAt.comp_hasDerivAt x hpath
  change deriv (fun ξ => uncurried γ (ξ, y)) x =
    fderiv ℝ (uncurried γ) (x, y) (1, 0)
  simpa [Function.comp_def] using hcomp.deriv

theorem partialY_eq_fderiv_uncurried
    {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (h : DifferentiableAt ℝ (uncurried γ) (x, y)) :
    partialY γ x y = fderiv ℝ (uncurried γ) (x, y) (0, 1) := by
  have hpath : HasDerivAt (fun η : ℝ => (x, η)) (0, 1) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  have hcomp := h.hasFDerivAt.comp_hasDerivAt y hpath
  change deriv (fun η => uncurried γ (x, η)) y =
    fderiv ℝ (uncurried γ) (x, y) (0, 1)
  simpa [Function.comp_def] using hcomp.deriv

/-- Real analyticity of the actual two-variable function supplies all six
calculus hypotheses of `DifferentialBridge`, including equality of the two
mixed partials. -/
theorem gammaDifferentialDataAt_of_analyticAt
    {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hγ : AnalyticAt ℝ (uncurried γ) (x, y)) :
    GammaDifferentialDataAt γ x y := by
  let f : ℝ × ℝ → ℝ := uncurried γ
  let vx : ℝ × ℝ := (1, 0)
  let vy : ℝ × ℝ := (0, 1)
  have hpathX : AnalyticAt ℝ (fun ξ : ℝ => (ξ, y)) x :=
    analyticAt_id.prod analyticAt_const
  have hpathY : AnalyticAt ℝ (fun η : ℝ => (x, η)) y :=
    analyticAt_const.prod analyticAt_id
  have hsliceX : AnalyticAt ℝ (fun ξ => γ ξ y) x := by
    simpa [Function.comp_def, uncurried] using
      hγ.comp (f := fun ξ : ℝ => (ξ, y)) hpathX
  have hsliceY : AnalyticAt ℝ (γ x) y := by
    simpa [Function.comp_def, uncurried] using
      hγ.comp (f := fun η : ℝ => (x, η)) hpathY
  have hdx : HasDerivAt (fun ξ => γ ξ y) (partialX γ x y) x := by
    simpa only [partialX] using hsliceX.differentiableAt.hasDerivAt
  have hdy : HasDerivAt (γ x) (partialY γ x y) y := by
    simpa only [partialY] using hsliceY.differentiableAt.hasDerivAt
  have hdxx :
      HasDerivAt (fun ξ => partialX γ ξ y) (partialXX γ x y) x := by
    simpa only [partialX, partialXX] using
      hsliceX.deriv.differentiableAt.hasDerivAt
  have hdyy :
      HasDerivAt (fun η => partialY γ x η) (partialYY γ x y) y := by
    simpa only [partialY, partialYY] using
      hsliceY.deriv.differentiableAt.hasDerivAt
  have hfderAnalytic : AnalyticAt ℝ (fderiv ℝ f) (x, y) := by
    simpa only [f] using hγ.fderiv
  have hfderCont : ContDiffAt ℝ ω (fderiv ℝ f) (x, y) :=
    hfderAnalytic.contDiffAt
  have hFx : AnalyticAt ℝ (fun z => fderiv ℝ f z vx) (x, y) := by
    exact (hfderCont.clm_apply contDiffAt_const).analyticAt
  have hFy : AnalyticAt ℝ (fun z => fderiv ℝ f z vy) (x, y) := by
    exact (hfderCont.clm_apply contDiffAt_const).analyticAt
  have hFxPath : AnalyticAt ℝ (fun η => fderiv ℝ f (x, η) vx) y :=
    hFx.comp (f := fun η : ℝ => (x, η)) hpathY
  have hFyPath : AnalyticAt ℝ (fun ξ => fderiv ℝ f (ξ, y) vy) x :=
    hFy.comp (f := fun ξ : ℝ => (ξ, y)) hpathX
  have hevX : ∀ᶠ η in nhds y, AnalyticAt ℝ f (x, η) :=
    hpathY.continuousAt hγ.eventually_analyticAt
  have hevY : ∀ᶠ ξ in nhds x, AnalyticAt ℝ f (ξ, y) :=
    hpathX.continuousAt hγ.eventually_analyticAt
  have heqX :
      (fun η => partialX γ x η) =ᶠ[nhds y]
        (fun η => fderiv ℝ f (x, η) vx) := by
    filter_upwards [hevX] with η hη
    simpa only [f, vx] using partialX_eq_fderiv_uncurried hη.differentiableAt
  have heqY :
      (fun ξ => partialY γ ξ y) =ᶠ[nhds x]
        (fun ξ => fderiv ℝ f (ξ, y) vy) := by
    filter_upwards [hevY] with ξ hξ
    simpa only [f, vy] using partialY_eq_fderiv_uncurried hξ.differentiableAt
  have hdxyDiff : DifferentiableAt ℝ (fun η => partialX γ x η) y :=
    hFxPath.differentiableAt.congr_of_eventuallyEq heqX
  have hdyxDiff : DifferentiableAt ℝ (fun ξ => partialY γ ξ y) x :=
    hFyPath.differentiableAt.congr_of_eventuallyEq heqY
  have hdxy :
      HasDerivAt (fun η => partialX γ x η) (partialXY γ x y) y := by
    simpa only [partialXY] using hdxyDiff.hasDerivAt
  let D2 : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
    fderiv ℝ (fderiv ℝ f) (x, y)
  have hFderiv : HasFDerivAt (fderiv ℝ f) D2 (x, y) := by
    simpa only [D2] using hfderAnalytic.differentiableAt.hasFDerivAt
  have hFxFull : HasFDerivAt (fun z => fderiv ℝ f z vx) (D2.flip vx) (x, y) := by
    simpa using hFderiv.clm_apply
      (hasFDerivAt_const vx (x, y))
  have hFyFull : HasFDerivAt (fun z => fderiv ℝ f z vy) (D2.flip vy) (x, y) := by
    simpa using hFderiv.clm_apply
      (hasFDerivAt_const vy (x, y))
  have hFxDeriv :
      deriv (fun η => fderiv ℝ f (x, η) vx) y = D2 vy vx := by
    have hcomp := hFxFull.comp_hasDerivAt y
      ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
    simpa [Function.comp_def, vx, vy] using hcomp.deriv
  have hFyDeriv :
      deriv (fun ξ => fderiv ℝ f (ξ, y) vy) x = D2 vx vy := by
    have hcomp := hFyFull.comp_hasDerivAt x
      ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
    simpa [Function.comp_def, vx, vy] using hcomp.deriv
  have hsymm : D2 vy vx = D2 vx vy := by
    have hs : IsSymmSndFDerivAt ℝ f (x, y) :=
      (by simpa only [f] using
        (hγ.contDiffAt (n := ω)).isSymmSndFDerivAt (by simp))
    simpa only [D2] using hs.eq vy vx
  have hmixed :
      deriv (fun ξ => partialY γ ξ y) x = partialXY γ x y := by
    rw [partialXY, heqY.deriv_eq, heqX.deriv_eq, hFyDeriv, hFxDeriv]
    exact hsymm.symm
  have hdyx :
      HasDerivAt (fun ξ => partialY γ ξ y) (partialXY γ x y) x :=
    hdyxDiff.hasDerivAt.congr_deriv hmixed
  exact ⟨hdx, hdxx, hdyx, hdy, hdxy, hdyy⟩

/-- At an analytic point, the project's mixed partial is the corresponding
evaluation of the second Fréchet derivative. -/
theorem partialXY_eq_secondFDeriv_uncurried
    {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hγ : AnalyticAt ℝ (uncurried γ) (x, y)) :
    partialXY γ x y =
      fderiv ℝ (fderiv ℝ (uncurried γ)) (x, y) (0, 1) (1, 0) := by
  let f : ℝ × ℝ → ℝ := uncurried γ
  let vx : ℝ × ℝ := (1, 0)
  let vy : ℝ × ℝ := (0, 1)
  have hpathY : AnalyticAt ℝ (fun η : ℝ => (x, η)) y :=
    analyticAt_const.prod analyticAt_id
  have hfderAnalytic : AnalyticAt ℝ (fderiv ℝ f) (x, y) := by
    simpa only [f] using hγ.fderiv
  have hFx : AnalyticAt ℝ (fun z => fderiv ℝ f z vx) (x, y) := by
    exact (hfderAnalytic.contDiffAt.clm_apply contDiffAt_const).analyticAt
  have hFxPath : AnalyticAt ℝ (fun η => fderiv ℝ f (x, η) vx) y :=
    hFx.comp (f := fun η : ℝ => (x, η)) hpathY
  have hev : ∀ᶠ η in nhds y, AnalyticAt ℝ f (x, η) :=
    hpathY.continuousAt hγ.eventually_analyticAt
  have heq :
      (fun η => partialX γ x η) =ᶠ[nhds y]
        (fun η => fderiv ℝ f (x, η) vx) := by
    filter_upwards [hev] with η hη
    simpa only [f, vx] using partialX_eq_fderiv_uncurried hη.differentiableAt
  let D2 : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
    fderiv ℝ (fderiv ℝ f) (x, y)
  have hFderiv : HasFDerivAt (fderiv ℝ f) D2 (x, y) := by
    simpa only [D2] using hfderAnalytic.differentiableAt.hasFDerivAt
  have hFxFull : HasFDerivAt (fun z => fderiv ℝ f z vx) (D2.flip vx) (x, y) := by
    simpa using hFderiv.clm_apply (hasFDerivAt_const vx (x, y))
  have hcomp := hFxFull.comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
  rw [partialXY, heq.deriv_eq]
  simpa [Function.comp_def, f, vx, vy, D2] using hcomp.deriv

/-- At an analytic point, the project's pure `y` second partial is the
corresponding evaluation of the second Fréchet derivative. -/
theorem partialYY_eq_secondFDeriv_uncurried
    {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hγ : AnalyticAt ℝ (uncurried γ) (x, y)) :
    partialYY γ x y =
      fderiv ℝ (fderiv ℝ (uncurried γ)) (x, y) (0, 1) (0, 1) := by
  let f : ℝ × ℝ → ℝ := uncurried γ
  let vy : ℝ × ℝ := (0, 1)
  have hpathY : AnalyticAt ℝ (fun η : ℝ => (x, η)) y :=
    analyticAt_const.prod analyticAt_id
  have hfderAnalytic : AnalyticAt ℝ (fderiv ℝ f) (x, y) := by
    simpa only [f] using hγ.fderiv
  have hFy : AnalyticAt ℝ (fun z => fderiv ℝ f z vy) (x, y) := by
    exact (hfderAnalytic.contDiffAt.clm_apply contDiffAt_const).analyticAt
  have hFyPath : AnalyticAt ℝ (fun η => fderiv ℝ f (x, η) vy) y :=
    hFy.comp (f := fun η : ℝ => (x, η)) hpathY
  have hev : ∀ᶠ η in nhds y, AnalyticAt ℝ f (x, η) :=
    hpathY.continuousAt hγ.eventually_analyticAt
  have heq :
      (fun η => partialY γ x η) =ᶠ[nhds y]
        (fun η => fderiv ℝ f (x, η) vy) := by
    filter_upwards [hev] with η hη
    simpa only [f, vy] using partialY_eq_fderiv_uncurried hη.differentiableAt
  let D2 : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
    fderiv ℝ (fderiv ℝ f) (x, y)
  have hFderiv : HasFDerivAt (fderiv ℝ f) D2 (x, y) := by
    simpa only [D2] using hfderAnalytic.differentiableAt.hasFDerivAt
  have hFyFull : HasFDerivAt (fun z => fderiv ℝ f z vy) (D2.flip vy) (x, y) := by
    simpa using hFderiv.clm_apply (hasFDerivAt_const vy (x, y))
  have hcomp := hFyFull.comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
  rw [partialYY, heq.deriv_eq]
  simpa [Function.comp_def, f, vy, D2] using hcomp.deriv

/-! ## Chain rules with the analytic scalar hypothesis discharged -/

theorem hasDerivAt_scalarField_x_of_gamma0_of_scalarAnalytic
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y gx : ℝ}
    (hgamma0 : HasDerivAt (fun ξ => gamma0Field γ ξ y) gx x)
    (hscalar : (y, gamma0Field γ x y) ∈ scalarAnalyticRegion P) :
    HasDerivAt (fun ξ => scalarField P γ ξ y)
      ((scalarDataField P γ x y).dSdd * gx) x :=
  hasDerivAt_scalarField_x_of_gamma0 hgamma0
    (hasFDerivAt_stildeUncurried_scalarDataField_of_mem hscalar)

theorem hasDerivAt_scalarField_y_of_gamma0_of_scalarAnalytic
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y gy : ℝ}
    (hgamma0 : HasDerivAt (fun η => gamma0Field γ x η) gy y)
    (hscalar : (y, gamma0Field γ x y) ∈ scalarAnalyticRegion P) :
    HasDerivAt (fun η => scalarField P γ x η)
      ((scalarDataField P γ x y).dSdt +
        (scalarDataField P γ x y).dSdd * gy) y :=
  hasDerivAt_scalarField_y_of_gamma0 hgamma0
    (hasFDerivAt_stildeUncurried_scalarDataField_of_mem hscalar)

/-! ## Residual and divergence bridges without a separate scalar derivative -/

/-- The actual residual equals the polynomial residual once the composed
scalar point is in the analytic region.  Only regularity of `γ` remains as
an explicit calculus input. -/
theorem differentialResidual_eq_residualNormal_of_scalarAnalytic
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hx : HasDerivAt (fun ξ => γ ξ y) (partialX γ x y) x)
    (hxx : HasDerivAt (fun ξ => partialX γ ξ y) (partialXX γ x y) x)
    (hyx : HasDerivAt (fun ξ => partialY γ ξ y) (partialXY γ x y) x)
    (hy : HasDerivAt (γ x) (partialY γ x y) y)
    (hxy : HasDerivAt (fun η => partialX γ x η) (partialXY γ x y) y)
    (hyy : HasDerivAt (fun η => partialY γ x η) (partialYY γ x y) y)
    (hscalar : (y, gamma0Field γ x y) ∈ scalarAnalyticRegion P) :
    differentialResidual P γ x y =
      residualNormal P y (jetOf γ x y) (partialXX γ x y)
        (scalarDataField P γ x y) :=
  differentialResidual_eq_residualNormal hx hxx hyx hy hxy hyy
    (hasFDerivAt_stildeUncurried_scalarDataField_of_mem hscalar)

theorem differentialResidual_eq_zero_iff_auxiliaryEquationAt_of_scalarAnalytic
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hx : HasDerivAt (fun ξ => γ ξ y) (partialX γ x y) x)
    (hxx : HasDerivAt (fun ξ => partialX γ ξ y) (partialXX γ x y) x)
    (hyx : HasDerivAt (fun ξ => partialY γ ξ y) (partialXY γ x y) x)
    (hy : HasDerivAt (γ x) (partialY γ x y) y)
    (hxy : HasDerivAt (fun η => partialX γ x η) (partialXY γ x y) y)
    (hyy : HasDerivAt (fun η => partialY γ x η) (partialYY γ x y) y)
    (hscalar : (y, gamma0Field γ x y) ∈ scalarAnalyticRegion P) :
    differentialResidual P γ x y = 0 ↔ auxiliaryEquationAt P γ x y :=
  differentialResidual_eq_zero_iff_auxiliaryEquationAt hx hxx hyx hy hxy hyy
    (hasFDerivAt_stildeUncurried_scalarDataField_of_mem hscalar)

/-- If `γ` itself is analytic, the residual bridge needs no separate
one-variable derivative hypotheses. -/
theorem differentialResidual_eq_residualNormal_of_analyticAt
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hγ : AnalyticAt ℝ (uncurried γ) (x, y))
    (hscalar : (y, gamma0Field γ x y) ∈ scalarAnalyticRegion P) :
    differentialResidual P γ x y =
      residualNormal P y (jetOf γ x y) (partialXX γ x y)
        (scalarDataField P γ x y) := by
  have h := gammaDifferentialDataAt_of_analyticAt hγ
  exact differentialResidual_eq_residualNormal_of_scalarAnalytic
    h.dx h.dxx h.dyx h.dy h.dxy h.dyy hscalar

/-- Analyticity of `γ` and membership of the composed scalar point in the
analytic region identify the differential equation with the auxiliary
equation. -/
theorem differentialResidual_eq_zero_iff_auxiliaryEquationAt_of_analyticAt
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hγ : AnalyticAt ℝ (uncurried γ) (x, y))
    (hscalar : (y, gamma0Field γ x y) ∈ scalarAnalyticRegion P) :
    differentialResidual P γ x y = 0 ↔ auxiliaryEquationAt P γ x y := by
  have h := gammaDifferentialDataAt_of_analyticAt hγ
  exact differentialResidual_eq_zero_iff_auxiliaryEquationAt_of_scalarAnalytic
    h.dx h.dxx h.dyx h.dy h.dxy h.dyy hscalar

/-- The full off-axis divergence bridge with the scalar Fréchet derivative
derived from local analyticity. -/
theorem singularStressDivergence_eq_rpow_mul_residualNormal_of_scalarAnalytic
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ} (hy0 : y ≠ 0)
    (hx : HasDerivAt (fun ξ => γ ξ y) (partialX γ x y) x)
    (hxx : HasDerivAt (fun ξ => partialX γ ξ y) (partialXX γ x y) x)
    (hyx : HasDerivAt (fun ξ => partialY γ ξ y) (partialXY γ x y) x)
    (hy : HasDerivAt (γ x) (partialY γ x y) y)
    (hxy : HasDerivAt (fun η => partialX γ x η) (partialXY γ x y) y)
    (hyy : HasDerivAt (fun η => partialY γ x η) (partialYY γ x y) y)
    (hscalar : (y, gamma0Field γ x y) ∈ scalarAnalyticRegion P) :
    singularStressDivergence P γ x y =
      Real.rpow |y| (-(2 / P.p)) *
        residualNormal P y (jetOf γ x y) (partialXX γ x y)
          (scalarDataField P γ x y) :=
  singularStressDivergence_eq_rpow_mul_residualNormal hy0 hx hxx hyx hy hxy hyy
    (hasFDerivAt_stildeUncurried_scalarDataField_of_mem hscalar)

/-- Fully analytic version of the off-axis divergence bridge.  Its only
remaining pointwise assumptions are `y ≠ 0` and membership of
`(y,Γ₀[γ](x,y))` in the scalar analytic neighborhood. -/
theorem singularStressDivergence_eq_rpow_mul_residualNormal_of_analyticAt
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ} (hy0 : y ≠ 0)
    (hγ : AnalyticAt ℝ (uncurried γ) (x, y))
    (hscalar : (y, gamma0Field γ x y) ∈ scalarAnalyticRegion P) :
    singularStressDivergence P γ x y =
      Real.rpow |y| (-(2 / P.p)) *
        residualNormal P y (jetOf γ x y) (partialXX γ x y)
          (scalarDataField P γ x y) := by
  have h := gammaDifferentialDataAt_of_analyticAt hγ
  exact singularStressDivergence_eq_rpow_mul_residualNormal_of_scalarAnalytic
    hy0 h.dx h.dxx h.dyx h.dy h.dxy h.dyy hscalar

/-- On `U_q`, analyticity of `gamma` discharges every calculus and scalar
hypothesis in the off-axis divergence computation. -/
theorem singularStressDivergence_eq_rpow_mul_residualNormal_of_inU
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ} (hy0 : y ≠ 0)
    (hγ : AnalyticAt ℝ (uncurried γ) (x, y))
    (hU : InU P x y (jetOf γ x y)) :
    singularStressDivergence P γ x y =
      Real.rpow |y| (-(2 / P.p)) *
        residualNormal P y (jetOf γ x y) (partialXX γ x y)
          (scalarDataField P γ x y) := by
  exact singularStressDivergence_eq_rpow_mul_residualNormal_of_analyticAt
    hy0 hγ (scalarPoint_mem_scalarAnalyticRegion_of_inU hU)

end

end StressTensor
