import StressTensor.CompactLocalization
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Light rays of the localized ansatz

This file formalizes the definition of a maximally extended light segment in
(2.6)--(2.7) and applies it to the square supplied by
`CompactSquareLocalization`.

The metric in (2.6) is the Euclidean metric.  We spell it out because the
standard product metric on `ℝ × ℝ` is the max metric, rather than the
Euclidean metric used in the manuscript.
-/

namespace StressTensor

noncomputable section

/-! ## Euclidean segments and the definition from (2.6)--(2.7) -/

/-- The affine point `(1-t)a + tb`, written coordinatewise. -/
def affinePoint (a b : Point) (t : ℝ) : Point :=
  ((1 - t) * a.1 + t * b.1, (1 - t) * a.2 + t * b.2)

/-- The closed line segment with endpoints `a` and `b`. -/
def closedSegment (a b : Point) : Set Point :=
  {z | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = affinePoint a b t}

/-- The relative interior of a nondegenerate line segment. -/
def openSegment (a b : Point) : Set Point :=
  {z | ∃ t : ℝ, 0 < t ∧ t < 1 ∧ z = affinePoint a b t}

/-- Collinearity with the ordered pair `a,b`.  When `a ≠ b`, as in every
use below, this is the usual notion of collinearity. -/
def CollinearWith (a b z : Point) : Prop :=
  ∃ t : ℝ, z = affinePoint a b t

/-- Euclidean distance on the plane. -/
def planeDistance (a b : Point) : ℝ :=
  Real.sqrt ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2)

/-- For three collinear points, this is an elementary exact formulation of
"the smallest segment containing them has relative interior in `Omega`":
the segment between the two extreme points is one of the three pairwise
segments, and the other two are its subsegments. -/
def SmallestSegmentInteriorIn
    (Omega : Set Point) (a b z : Point) : Prop :=
  openSegment a b ⊆ Omega ∧
    openSegment a z ⊆ Omega ∧
    openSegment b z ⊆ Omega

/-- Equation (2.6): a nontrivial segment in `Omega` on which the endpoint
oscillation saturates the Euclidean Lipschitz bound. -/
def IsLightSegment
    (Omega : Set Point) (u : Point → ℝ) (a b : Point) : Prop :=
  a ∈ closure Omega ∧
    b ∈ closure Omega ∧
    a ≠ b ∧
    openSegment a b ⊆ Omega ∧
    |u a - u b| = planeDistance a b

/-- Equations (2.6)--(2.7): a light segment which cannot be extended while
retaining equality with either old endpoint. -/
def IsMaximallyExtendedLightSegment
    (Omega : Set Point) (u : Point → ℝ) (a b : Point) : Prop :=
  IsLightSegment Omega u a b ∧
    ∀ z ∈ closure Omega, z ∉ closedSegment a b →
      CollinearWith a b z →
      SmallestSegmentInteriorIn Omega a b z →
      |u a - u z| < planeDistance a z ∨
        |u b - u z| < planeDistance b z

/-- The set `Sigma` of maximally extended light segments, represented by
ordered endpoint pairs. -/
def lightRays (Omega : Set Point) (u : Point → ℝ) : Set (Point × Point) :=
  {ab | IsMaximallyExtendedLightSegment Omega u ab.1 ab.2}

/-! ## Elementary horizontal-segment geometry -/

/-- The left endpoint of the horizontal diameter of the square. -/
def horizontalLeft (ell : ℝ) : Point := (-ell, 0)

/-- The right endpoint of the horizontal diameter of the square. -/
def horizontalRight (ell : ℝ) : Point := (ell, 0)

/-- The full horizontal diameter of the closed square. -/
def horizontalDiameter (ell : ℝ) : Set Point :=
  closedSegment (horizontalLeft ell) (horizontalRight ell)

@[simp] theorem planeDistance_horizontal (x₁ x₂ : ℝ) :
    planeDistance (x₁, 0) (x₂, 0) = |x₁ - x₂| := by
  simp [planeDistance, Real.sqrt_sq_eq_abs]

theorem openSegment_horizontal_subset_openSquare
    {ell x₁ x₂ : ℝ} (hell : 0 < ell)
    (hx₁ : |x₁| ≤ ell) (hx₂ : |x₂| ≤ ell) (hne : x₁ ≠ x₂) :
    openSegment (x₁, 0) (x₂, 0) ⊆ openSquare ell := by
  rintro z ⟨t, ht0, ht1, rfl⟩
  have hx₁' := abs_le.mp hx₁
  have hx₂' := abs_le.mp hx₂
  have hstrict :
      -ell < (1 - t) * x₁ + t * x₂ ∧
        (1 - t) * x₁ + t * x₂ < ell := by
    rcases lt_or_gt_of_ne hne with h₁₂ | h₂₁
    · constructor
      · have : x₁ < (1 - t) * x₁ + t * x₂ := by nlinarith
        exact lt_of_le_of_lt hx₁'.1 this
      · have : (1 - t) * x₁ + t * x₂ < x₂ := by nlinarith
        exact lt_of_lt_of_le this hx₂'.2
    · constructor
      · have : x₂ < (1 - t) * x₁ + t * x₂ := by nlinarith
        exact lt_of_le_of_lt hx₂'.1 this
      · have : (1 - t) * x₁ + t * x₂ < x₁ := by nlinarith
        exact lt_of_lt_of_le this hx₁'.2
  constructor
  · simpa [affinePoint, abs_lt] using hstrict
  · simpa [affinePoint] using hell

theorem closedSquare_collinear_mem_horizontalDiameter
    {ell : ℝ} (hell : 0 < ell) {z : Point}
    (hz : z ∈ closedSquare ell)
    (hcol : CollinearWith (horizontalLeft ell) (horizontalRight ell) z) :
    z ∈ horizontalDiameter ell := by
  rcases hcol with ⟨t, rfl⟩
  have hx := abs_le.mp hz.1
  refine ⟨t, ?_, ?_, rfl⟩
  · dsimp [affinePoint, horizontalLeft, horizontalRight] at hx ⊢
    nlinarith
  · dsimp [affinePoint, horizontalLeft, horizontalRight] at hx ⊢
    nlinarith

theorem closedSegment_comm (a b : Point) :
    closedSegment a b = closedSegment b a := by
  ext z
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    refine ⟨1 - t, by linarith, by linarith, ?_⟩
    ext <;> dsimp [affinePoint] <;> ring
  · rintro ⟨t, ht0, ht1, rfl⟩
    refine ⟨1 - t, by linarith, by linarith, ?_⟩
    ext <;> dsimp [affinePoint] <;> ring

theorem collinearWith_horizontal
    {x₁ x₂ x : ℝ} (hne : x₁ ≠ x₂) :
    CollinearWith (x₁, 0) (x₂, 0) (x, 0) := by
  refine ⟨(x - x₁) / (x₂ - x₁), ?_⟩
  ext
  · dsimp [affinePoint]
    field_simp [sub_ne_zero.mpr hne.symm]
    ring
  · simp [affinePoint]

theorem horizontalLeft_not_mem_closedSegment
    {ell x₁ x₂ : ℝ} (hx₁ : -ell < x₁) (hx₂ : -ell < x₂) :
    horizontalLeft ell ∉ closedSegment (x₁, 0) (x₂, 0) := by
  rintro ⟨t, ht0, ht1, heq⟩
  have heq₁ := congrArg Prod.fst heq
  dsimp [horizontalLeft, affinePoint] at heq₁
  have hx₁pos : 0 < x₁ + ell := by linarith
  have hx₂pos : 0 < x₂ + ell := by linarith
  have hweight₁ : 0 ≤ (1 - t) * (x₁ + ell) :=
    mul_nonneg (by linarith) hx₁pos.le
  have hweight₂ : 0 ≤ t * (x₂ + ell) :=
    mul_nonneg ht0 hx₂pos.le
  have hsum : 0 < (1 - t) * (x₁ + ell) + t * (x₂ + ell) := by
    by_cases ht : t = 0
    · subst t
      simpa using hx₁pos
    · exact add_pos_of_nonneg_of_pos hweight₁
        (mul_pos (lt_of_le_of_ne ht0 (Ne.symm ht)) hx₂pos)
  nlinarith

theorem horizontalRight_not_mem_closedSegment
    {ell x₁ x₂ : ℝ} (hx₁ : x₁ < ell) (hx₂ : x₂ < ell) :
    horizontalRight ell ∉ closedSegment (x₁, 0) (x₂, 0) := by
  rintro ⟨t, ht0, ht1, heq⟩
  have heq₁ := congrArg Prod.fst heq
  dsimp [horizontalRight, affinePoint] at heq₁
  have hx₁pos : 0 < ell - x₁ := by linarith
  have hx₂pos : 0 < ell - x₂ := by linarith
  have hweight₁ : 0 ≤ (1 - t) * (ell - x₁) :=
    mul_nonneg (by linarith) hx₁pos.le
  have hweight₂ : 0 ≤ t * (ell - x₂) :=
    mul_nonneg ht0 hx₂pos.le
  have hsum : 0 < (1 - t) * (ell - x₁) + t * (ell - x₂) := by
    by_cases ht : t = 0
    · subst t
      simpa using hx₁pos
    · exact add_pos_of_nonneg_of_pos hweight₁
        (mul_pos (lt_of_le_of_ne ht0 (Ne.symm ht)) hx₂pos)
  nlinarith

theorem ansatz_on_horizontal_axis (gamma : ℝ → ℝ → ℝ) (x : ℝ) :
    ansatz gamma x 0 = x := by
  simp [ansatz]

theorem ansatz_horizontal_saturates
    (gamma : ℝ → ℝ → ℝ) (x₁ x₂ : ℝ) :
    |ansatz gamma x₁ 0 - ansatz gamma x₂ 0| =
      planeDistance (x₁, 0) (x₂, 0) := by
  simp [ansatz_on_horizontal_axis]

/-! ## One-dimensional calculus along affine segments -/

/-- Convex combinations of two points in the closed square remain in the
closed square. -/
theorem closedSegment_subset_closedSquare
    {ell : ℝ} {a b : Point} (ha : a ∈ closedSquare ell)
    (hb : b ∈ closedSquare ell) :
    closedSegment a b ⊆ closedSquare ell := by
  rintro z ⟨t, ht0, ht1, rfl⟩
  have ha₁ := abs_le.mp ha.1
  have ha₂ := abs_le.mp ha.2
  have hb₁ := abs_le.mp hb.1
  have hb₂ := abs_le.mp hb.2
  constructor <;> rw [abs_le] <;>
    constructor <;> dsimp [affinePoint] <;> nlinarith

/-- Analyticity of `gamma` at a point gives differentiability of the
two-variable ansatz at that point. -/
theorem differentiableAt_uncurriedAnsatz_of_analyticAt
    {gamma : ℝ → ℝ → ℝ} {w : Point}
    (hgamma : AnalyticAt ℝ (uncurried gamma) w) :
    DifferentiableAt ℝ (fun v : Point => ansatz gamma v.1 v.2) w := by
  have hfst : AnalyticAt ℝ (fun v : Point => v.1) w := analyticAt_fst
  have hsnd : AnalyticAt ℝ (fun v : Point => v.2) w := analyticAt_snd
  have hu : AnalyticAt ℝ (fun v : Point => ansatz gamma v.1 v.2) w := by
    change AnalyticAt ℝ
      ((fun v : Point => v.1) + (fun v : Point => v.2) ^ 2 * uncurried gamma) w
    exact hfst.add ((hsnd.pow 2).mul hgamma)
  exact hu.differentiableAt

/-- The Fréchet derivative of a differentiable scalar function on a product
is reconstructed from its two ordinary partial derivatives. -/
theorem fderiv_prod_apply_eq_partialDerivs
    {f : Point → ℝ} {w v : Point} (hf : DifferentiableAt ℝ f w) :
    fderiv ℝ f w v =
      deriv (fun x : ℝ => f (x, w.2)) w.1 * v.1 +
        deriv (fun y : ℝ => f (w.1, y)) w.2 * v.2 := by
  have hx : deriv (fun x : ℝ => f (x, w.2)) w.1 =
      fderiv ℝ f w (1, 0) := by
    have hpath : HasDerivAt (fun x : ℝ => (x, w.2)) (1, 0) w.1 :=
      (hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2)
    have hcomp := hf.hasFDerivAt.comp_hasDerivAt w.1 hpath
    change deriv (fun x : ℝ => f (x, w.2)) w.1 =
      fderiv ℝ f w (1, 0)
    simpa [Function.comp_def] using hcomp.deriv
  have hy : deriv (fun y : ℝ => f (w.1, y)) w.2 =
      fderiv ℝ f w (0, 1) := by
    have hpath : HasDerivAt (fun y : ℝ => (w.1, y)) (0, 1) w.2 :=
      (hasDerivAt_const w.2 w.1).prodMk (hasDerivAt_id w.2)
    have hcomp := hf.hasFDerivAt.comp_hasDerivAt w.2 hpath
    change deriv (fun y : ℝ => f (w.1, y)) w.2 =
      fderiv ℝ f w (0, 1)
    simpa [Function.comp_def] using hcomp.deriv
  have hv : v = v.1 • (1, 0) + v.2 • (0, 1) := by
    ext <;> simp
  rw [hv, map_add, map_smul, map_smul, ← hx, ← hy]
  simp [smul_eq_mul, mul_comm]

/-- Derivative of the affine parametrization of a segment. -/
theorem hasDerivAt_affinePoint (a b : Point) (t : ℝ) :
    HasDerivAt (affinePoint a b) (b.1 - a.1, b.2 - a.2) t := by
  apply HasDerivAt.prodMk
  · convert (hasDerivAt_const t a.1).add
        ((hasDerivAt_id t).mul_const (b.1 - a.1)) using 1
    · funext s
      dsimp [affinePoint]
      ring
    · simp
  · convert (hasDerivAt_const t a.2).add
        ((hasDerivAt_id t).mul_const (b.2 - a.2)) using 1
    · funext s
      dsimp [affinePoint]
      ring
    · simp

/-- Differentiability and the chain-rule formula for the ansatz restricted
to an affine segment, expressed using `actualAnsatzGradient`. -/
theorem differentiableAt_ansatz_along_affinePoint
    {gamma : ℝ → ℝ → ℝ} {a b : Point} {t : ℝ}
    (hdiff : DifferentiableAt ℝ
      (fun w : Point => ansatz gamma w.1 w.2) (affinePoint a b t)) :
    DifferentiableAt ℝ
        (fun s : ℝ => ansatz gamma (affinePoint a b s).1
          (affinePoint a b s).2) t ∧
      deriv (fun s : ℝ => ansatz gamma (affinePoint a b s).1
          (affinePoint a b s).2) t =
        (actualAnsatzGradient gamma (affinePoint a b t).1
          (affinePoint a b t).2).1 * (b.1 - a.1) +
        (actualAnsatzGradient gamma (affinePoint a b t).1
          (affinePoint a b t).2).2 * (b.2 - a.2) := by
  have hchain := hdiff.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_affinePoint a b t)
  constructor
  · exact hchain.differentiableAt
  · have hderiv := hchain.deriv
    change deriv (fun s : ℝ => ansatz gamma (affinePoint a b s).1
        (affinePoint a b s).2) t =
      fderiv ℝ (fun w : Point => ansatz gamma w.1 w.2)
        (affinePoint a b t) (b.1 - a.1, b.2 - a.2) at hderiv
    rw [fderiv_prod_apply_eq_partialDerivs hdiff] at hderiv
    exact hderiv

/-- The two-dimensional Cauchy--Schwarz estimate, stated using the explicit
Euclidean quantities of this file. -/
theorem abs_dot_le_planeDistance_of_normSq_le_one
    {g a b : Point} (hg : normSq g ≤ 1) :
    |g.1 * (b.1 - a.1) + g.2 * (b.2 - a.2)| ≤ planeDistance a b := by
  have hsum : 0 ≤ (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 := by positivity
  have hdistSq : planeDistance a b ^ 2 =
      (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 := by
    rw [planeDistance, Real.sq_sqrt hsum]
  have hCauchy :
      (g.1 * (b.1 - a.1) + g.2 * (b.2 - a.2)) ^ 2 ≤
        normSq g * ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) := by
    have hcross := sq_nonneg
      (g.1 * (b.2 - a.2) - g.2 * (b.1 - a.1))
    dsimp [normSq] at hg ⊢
    nlinarith
  have hscale :
      normSq g * ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) ≤
        (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 := by
    have := mul_nonneg (sub_nonneg.mpr hg) hsum
    nlinarith
  apply abs_le_of_sq_le_sq
  · rw [hdistSq]
    exact hCauchy.trans hscale
  · exact Real.sqrt_nonneg _

/-- Equality in the preceding Cauchy--Schwarz estimate, for a nonzero
direction, forces the gradient to have Euclidean norm one. -/
theorem normSq_eq_one_of_abs_dot_eq_planeDistance
    {g a b : Point} (hab : a ≠ b) (hg : normSq g ≤ 1)
    (heq : |g.1 * (b.1 - a.1) + g.2 * (b.2 - a.2)| =
      planeDistance a b) :
    normSq g = 1 := by
  have hsumNonneg : 0 ≤ (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 := by positivity
  have hsumPos : 0 < (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 := by
    apply lt_of_le_of_ne hsumNonneg
    intro hzero
    apply hab
    ext
    · nlinarith [sq_nonneg (a.1 - b.1), sq_nonneg (a.2 - b.2)]
    · nlinarith [sq_nonneg (a.1 - b.1), sq_nonneg (a.2 - b.2)]
  have hdistSq : planeDistance a b ^ 2 =
      (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 := by
    rw [planeDistance, Real.sq_sqrt hsumNonneg]
  have heqSq := congrArg (fun r : ℝ => r ^ 2) heq
  have hdotSq :
      (g.1 * (b.1 - a.1) + g.2 * (b.2 - a.2)) ^ 2 =
        planeDistance a b ^ 2 := by
    simpa only [sq_abs] using heqSq
  have hCauchy :
      (g.1 * (b.1 - a.1) + g.2 * (b.2 - a.2)) ^ 2 ≤
        normSq g * ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) := by
    have hcross := sq_nonneg
      (g.1 * (b.2 - a.2) - g.2 * (b.1 - a.1))
    dsimp [normSq] at hg ⊢
    nlinarith
  have hsumLe :
      (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 ≤
        normSq g * ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) := by
    calc
      (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 =
          planeDistance a b ^ 2 := hdistSq.symm
      _ = (g.1 * (b.1 - a.1) + g.2 * (b.2 - a.2)) ^ 2 := hdotSq.symm
      _ ≤ normSq g * ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) := hCauchy
  have hge : 1 ≤ normSq g := by
    apply le_of_mul_le_mul_right _ hsumPos
    simpa only [one_mul] using hsumLe
  exact le_antisymm hg hge

/-! ## The horizontal diameter is a maximal light segment -/

theorem horizontalDiameter_isLightSegment
    (gamma : ℝ → ℝ → ℝ) {ell : ℝ} (hell : 0 < ell) :
    IsLightSegment (openSquare ell)
      (fun w => ansatz gamma w.1 w.2)
      (horizontalLeft ell) (horizontalRight ell) := by
  rw [IsLightSegment, closure_openSquare hell]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · simp [horizontalLeft, abs_of_nonneg hell.le]
    · simpa [horizontalLeft] using hell.le
  · constructor
    · simp [horizontalRight, abs_of_nonneg hell.le]
    · simpa [horizontalRight] using hell.le
  · intro h
    have := congrArg Prod.fst h
    dsimp [horizontalLeft, horizontalRight] at this
    linarith
  · apply openSegment_horizontal_subset_openSquare hell
    · simp [abs_of_nonneg hell.le]
    · simp [abs_of_nonneg hell.le]
    · dsimp [horizontalLeft, horizontalRight]
      linarith
  · exact ansatz_horizontal_saturates gamma (-ell) ell

theorem horizontalDiameter_isMaximallyExtendedLightSegment
    (gamma : ℝ → ℝ → ℝ) {ell : ℝ} (hell : 0 < ell) :
    IsMaximallyExtendedLightSegment (openSquare ell)
      (fun w => ansatz gamma w.1 w.2)
      (horizontalLeft ell) (horizontalRight ell) := by
  refine ⟨horizontalDiameter_isLightSegment gamma hell, ?_⟩
  intro z hz hzout hcol _hinterior
  rw [closure_openSquare hell] at hz
  exact (hzout (closedSquare_collinear_mem_horizontalDiameter hell hz hcol)).elim

/-! ## Rigidity and uniqueness -/

/-- The norm-one consequence of the standard interior rigidity lemma for a
function saturating a 1-Lipschitz bound on a segment (the result cited after
(2.7) in the reference), packaged as a reusable property.  For the localized
analytic ansatz this property is proved immediately below. -/
def LightSegmentInteriorNormRigidity
    (Omega : Set Point) (u : Point → ℝ) (gradient : Point → Point) : Prop :=
  ∀ {a b z : Point}, IsLightSegment Omega u a b → z ∈ openSegment a b →
    normSq (gradient z) = 1

/-- The standard interior rigidity statement is automatic for the localized
analytic ansatz.  The proof is one-dimensional: restrict the ansatz to the
segment, use the pointwise Euclidean gradient bound and Cauchy--Schwarz in
the mean-value inequality, and use endpoint saturation to force the
restriction to be affine. -/
theorem lightSegmentInteriorNormRigidity_localizedAnsatz
    {P : Params} {gamma : ℝ → ℝ → ℝ} {U : Set Point}
    (L : CompactSquareLocalization P gamma U)
    (hanalytic : AnalyticOnNhd ℝ (uncurried gamma) U) :
    LightSegmentInteriorNormRigidity
      (openSquare L.ell) (fun w => ansatz gamma w.1 w.2)
      (fun w => actualAnsatzGradient gamma w.1 w.2) := by
  intro a b z hlight hz
  rcases hz with ⟨t, ht0, ht1, rfl⟩
  rcases hlight with ⟨haClosure, hbClosure, hab, hopen, hsaturates⟩
  rw [closure_openSquare L.ell_pos] at haClosure hbClosure
  let f : ℝ → ℝ := fun s =>
    ansatz gamma (affinePoint a b s).1 (affinePoint a b s).2
  let D : ℝ := planeDistance a b
  have hcalc : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℝ f s ∧
        deriv f s =
          (actualAnsatzGradient gamma (affinePoint a b s).1
              (affinePoint a b s).2).1 * (b.1 - a.1) +
            (actualAnsatzGradient gamma (affinePoint a b s).1
              (affinePoint a b s).2).2 * (b.2 - a.2) := by
    intro s hs
    have hwClosed : affinePoint a b s ∈ closedSquare L.ell :=
      closedSegment_subset_closedSquare haClosure hbClosure
        ⟨s, hs.1, hs.2, rfl⟩
    have hdiff : DifferentiableAt ℝ
        (fun w : Point => ansatz gamma w.1 w.2) (affinePoint a b s) :=
      differentiableAt_uncurriedAnsatz_of_analyticAt
        (hanalytic _ (L.closed_subset_domain hwClosed))
    simpa only [f] using differentiableAt_ansatz_along_affinePoint hdiff
  have hnormLe : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      normSq (actualAnsatzGradient gamma (affinePoint a b s).1
        (affinePoint a b s).2) ≤ 1 := by
    intro s hs
    have hwClosed : affinePoint a b s ∈ closedSquare L.ell :=
      closedSegment_subset_closedSquare haClosure hbClosure
        ⟨s, hs.1, hs.2, rfl⟩
    by_cases hy : (affinePoint a b s).2 = 0
    · rw [hy]
      exact (L.normSq_actualAnsatzGradient_axis hanalytic
        (by
          convert hwClosed using 1
          ext <;> simp [hy])).le
    · exact (L.normSq_actualAnsatzGradient_lt_one
        hanalytic hwClosed hy).le
  have hderivBound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖deriv f s‖ ≤ D := by
    intro s hs
    rw [(hcalc s hs).2, Real.norm_eq_abs]
    exact abs_dot_le_planeDistance_of_normSq_le_one (hnormLe s hs)
  have hdiffPath : ∀ s ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ f s :=
    fun s hs => (hcalc s hs).1
  have hLip : ∀ {s r : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      r ∈ Set.Icc (0 : ℝ) 1 →
      |f r - f s| ≤ D * |r - s| := by
    intro s r hs hr
    simpa only [Real.norm_eq_abs] using
      (Convex.norm_image_sub_le_of_norm_deriv_le
        hdiffPath hderivBound (convex_Icc 0 1) hs hr)
  have hD : 0 ≤ D := by
    exact Real.sqrt_nonneg _
  have hSatF : |f 1 - f 0| = D := by
    simpa [f, D, affinePoint, abs_sub_comm] using hsaturates
  have hzeroMem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have honeMem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hfromZero : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      |f s - f 0| ≤ D * s := by
    intro s hs
    simpa [abs_of_nonneg hs.1] using hLip hzeroMem hs
  have htoOne : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      |f 1 - f s| ≤ D * (1 - s) := by
    intro s hs
    simpa [abs_of_nonneg (sub_nonneg.mpr hs.2)] using hLip hs honeMem
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0.le, ht1.le⟩
  have hdotAbs :
      |(actualAnsatzGradient gamma (affinePoint a b t).1
            (affinePoint a b t).2).1 * (b.1 - a.1) +
        (actualAnsatzGradient gamma (affinePoint a b t).1
            (affinePoint a b t).2).2 * (b.2 - a.2)| = D := by
    by_cases hsign : 0 ≤ f 1 - f 0
    · have hend : f 1 - f 0 = D := by
        calc
          f 1 - f 0 = |f 1 - f 0| := (abs_of_nonneg hsign).symm
          _ = D := hSatF
      have heqOn : ∀ s ∈ Set.Icc (0 : ℝ) 1,
          f s = f 0 + D * s := by
        intro s hs
        have hleft : f s - f 0 ≤ D * s :=
          (le_abs_self (f s - f 0)).trans (hfromZero s hs)
        have hright : f 1 - f s ≤ D * (1 - s) :=
          (le_abs_self (f 1 - f s)).trans (htoOne s hs)
        linarith
      have hev : f =ᶠ[nhds t] (fun s : ℝ => f 0 + D * s) := by
        filter_upwards [Icc_mem_nhds ht0 ht1] with s hs
        exact heqOn s hs
      have hderivAffine : deriv f t = D := by
        rw [hev.deriv_eq]
        simp
      have hdot := (hcalc t htIcc).2
      rw [hderivAffine] at hdot
      rw [← hdot, abs_of_nonneg hD]
    · have hneg : f 1 - f 0 < 0 := lt_of_not_ge hsign
      have hend : f 0 - f 1 = D := by
        calc
          f 0 - f 1 = -(f 1 - f 0) := by ring
          _ = |f 1 - f 0| := (abs_of_neg hneg).symm
          _ = D := hSatF
      have heqOn : ∀ s ∈ Set.Icc (0 : ℝ) 1,
          f s = f 0 - D * s := by
        intro s hs
        have hleft : f 0 - f s ≤ D * s := by
          calc
            f 0 - f s ≤ |f 0 - f s| := le_abs_self _
            _ = |f s - f 0| := abs_sub_comm _ _
            _ ≤ D * s := hfromZero s hs
        have hright : f s - f 1 ≤ D * (1 - s) := by
          calc
            f s - f 1 ≤ |f s - f 1| := le_abs_self _
            _ = |f 1 - f s| := abs_sub_comm _ _
            _ ≤ D * (1 - s) := htoOne s hs
        linarith
      have hev : f =ᶠ[nhds t] (fun s : ℝ => f 0 - D * s) := by
        filter_upwards [Icc_mem_nhds ht0 ht1] with s hs
        exact heqOn s hs
      have hderivAffine : deriv f t = -D := by
        rw [hev.deriv_eq]
        simp
      have hdot := (hcalc t htIcc).2
      rw [hderivAffine] at hdot
      rw [← hdot, abs_neg, abs_of_nonneg hD]
  apply normSq_eq_one_of_abs_dot_eq_planeDistance hab (hnormLe t htIcc)
  simpa only [D] using hdotAbs

theorem lightSegment_endpoints_on_horizontal_axis
    {P : Params} {gamma : ℝ → ℝ → ℝ} {U : Set Point}
    (L : CompactSquareLocalization P gamma U)
    (hanalytic : AnalyticOnNhd ℝ (uncurried gamma) U)
    (hrigidity : LightSegmentInteriorNormRigidity
      (openSquare L.ell) (fun w => ansatz gamma w.1 w.2)
      (fun w => actualAnsatzGradient gamma w.1 w.2))
    {a b : Point}
    (hlight : IsLightSegment (openSquare L.ell)
      (fun w => ansatz gamma w.1 w.2) a b) :
    a.2 = 0 ∧ b.2 = 0 := by
  have hinterior : ∀ z ∈ openSegment a b, z.2 = 0 := by
    intro z hz
    have hzopen := hlight.2.2.2.1 hz
    have hzclosed : z ∈ closedSquare L.ell := ⟨hzopen.1.le, hzopen.2.le⟩
    by_contra hy
    have hlt := L.normSq_actualAnsatzGradient_lt_one hanalytic hzclosed hy
    have heq := hrigidity hlight hz
    linarith
  have hz₁ : affinePoint a b (1 / 3 : ℝ) ∈ openSegment a b := by
    refine ⟨1 / 3, by norm_num, by norm_num, rfl⟩
  have hz₂ : affinePoint a b (2 / 3 : ℝ) ∈ openSegment a b := by
    refine ⟨2 / 3, by norm_num, by norm_num, rfl⟩
  have hy₁ := hinterior _ hz₁
  have hy₂ := hinterior _ hz₂
  dsimp [affinePoint] at hy₁ hy₂
  constructor <;> linarith

/-- A maximal light segment for the ansatz whose endpoints already lie on
the horizontal axis must have the two boundary points as its endpoints (in
one of the two possible orders). -/
theorem maximalHorizontalLightSegment_endpoints
    (gamma : ℝ → ℝ → ℝ) {ell x₁ x₂ : ℝ} (hell : 0 < ell)
    (hmax : IsMaximallyExtendedLightSegment (openSquare ell)
      (fun w => ansatz gamma w.1 w.2) (x₁, 0) (x₂, 0)) :
    (x₁ = -ell ∧ x₂ = ell) ∨ (x₁ = ell ∧ x₂ = -ell) := by
  rcases hmax.1 with ⟨hx₁Closure, hx₂Closure, hnePoint, hopen, _hsaturates⟩
  rw [closure_openSquare hell] at hx₁Closure hx₂Closure
  have hx₁ : |x₁| ≤ ell := hx₁Closure.1
  have hx₂ : |x₂| ≤ ell := hx₂Closure.1
  have hx₁Bounds := abs_le.mp hx₁
  have hx₂Bounds := abs_le.mp hx₂
  have hne : x₁ ≠ x₂ := by
    intro h
    apply hnePoint
    ext <;> simp [h]
  have hleftClosure : horizontalLeft ell ∈ closure (openSquare ell) := by
    rw [closure_openSquare hell]
    constructor
    · simp [horizontalLeft, abs_of_nonneg hell.le]
    · simpa [horizontalLeft] using hell.le
  have hrightClosure : horizontalRight ell ∈ closure (openSquare ell) := by
    rw [closure_openSquare hell]
    constructor
    · simp [horizontalRight, abs_of_nonneg hell.le]
    · simpa [horizontalRight] using hell.le
  have hleft : x₁ = -ell ∨ x₂ = -ell := by
    by_contra h
    have hx₁ne : x₁ ≠ -ell := fun hx => h (Or.inl hx)
    have hx₂ne : x₂ ≠ -ell := fun hx => h (Or.inr hx)
    have hx₁Left : -ell < x₁ :=
      lt_of_le_of_ne hx₁Bounds.1 hx₁ne.symm
    have hx₂Left : -ell < x₂ :=
      lt_of_le_of_ne hx₂Bounds.1 hx₂ne.symm
    have hzout : horizontalLeft ell ∉ closedSegment (x₁, 0) (x₂, 0) :=
      horizontalLeft_not_mem_closedSegment hx₁Left hx₂Left
    have hcol : CollinearWith (x₁, 0) (x₂, 0) (horizontalLeft ell) := by
      simpa [horizontalLeft] using
        (collinearWith_horizontal (x := -ell) hne)
    have hinterior : SmallestSegmentInteriorIn (openSquare ell)
        (x₁, 0) (x₂, 0) (horizontalLeft ell) := by
      refine ⟨hopen, ?_, ?_⟩
      · simpa [horizontalLeft] using
          (openSegment_horizontal_subset_openSquare hell hx₁
            (by simp [abs_of_nonneg hell.le]) hx₁ne)
      · simpa [horizontalLeft] using
          (openSegment_horizontal_subset_openSquare hell hx₂
            (by simp [abs_of_nonneg hell.le]) hx₂ne)
    have hstrict := hmax.2 (horizontalLeft ell) hleftClosure hzout hcol hinterior
    simp [horizontalLeft, ansatz_on_horizontal_axis] at hstrict
  have hright : x₁ = ell ∨ x₂ = ell := by
    by_contra h
    have hx₁ne : x₁ ≠ ell := fun hx => h (Or.inl hx)
    have hx₂ne : x₂ ≠ ell := fun hx => h (Or.inr hx)
    have hx₁Right : x₁ < ell :=
      lt_of_le_of_ne hx₁Bounds.2 hx₁ne
    have hx₂Right : x₂ < ell :=
      lt_of_le_of_ne hx₂Bounds.2 hx₂ne
    have hzout : horizontalRight ell ∉ closedSegment (x₁, 0) (x₂, 0) :=
      horizontalRight_not_mem_closedSegment hx₁Right hx₂Right
    have hcol : CollinearWith (x₁, 0) (x₂, 0) (horizontalRight ell) := by
      simpa [horizontalRight] using
        (collinearWith_horizontal (x := ell) hne)
    have hinterior : SmallestSegmentInteriorIn (openSquare ell)
        (x₁, 0) (x₂, 0) (horizontalRight ell) := by
      refine ⟨hopen, ?_, ?_⟩
      · simpa [horizontalRight] using
          (openSegment_horizontal_subset_openSquare hell hx₁
            (by simp [abs_of_nonneg hell.le]) hx₁ne)
      · simpa [horizontalRight] using
          (openSegment_horizontal_subset_openSquare hell hx₂
            (by simp [abs_of_nonneg hell.le]) hx₂ne)
    have hstrict := hmax.2 (horizontalRight ell) hrightClosure hzout hcol hinterior
    simp [horizontalRight, ansatz_on_horizontal_axis] at hstrict
  rcases hleft with hx₁Left | hx₂Left
  · rcases hright with hx₁Right | hx₂Right
    · exfalso
      linarith
    · exact Or.inl ⟨hx₁Left, hx₂Right⟩
  · rcases hright with hx₁Right | hx₂Right
    · exact Or.inr ⟨hx₁Right, hx₂Left⟩
    · exfalso
      linarith

/-- Generic final uniqueness from interior norm-rigidity.  Strict off-axis
spacelikeness forces every light segment onto the axis, and maximality forces
the full diameter. -/
theorem uniqueMaximalLightRay_of_interiorNormRigidity
    {P : Params} {gamma : ℝ → ℝ → ℝ} {U : Set Point}
    (L : CompactSquareLocalization P gamma U)
    (hanalytic : AnalyticOnNhd ℝ (uncurried gamma) U)
    (hrigidity : LightSegmentInteriorNormRigidity
      (openSquare L.ell) (fun w => ansatz gamma w.1 w.2)
      (fun w => actualAnsatzGradient gamma w.1 w.2))
    {a b : Point}
    (hmax : IsMaximallyExtendedLightSegment (openSquare L.ell)
      (fun w => ansatz gamma w.1 w.2) a b) :
    closedSegment a b = horizontalDiameter L.ell := by
  have haxis := lightSegment_endpoints_on_horizontal_axis
    L hanalytic hrigidity hmax.1
  rcases a with ⟨x₁, y₁⟩
  rcases b with ⟨x₂, y₂⟩
  dsimp at haxis ⊢
  rcases haxis with ⟨hy₁, hy₂⟩
  subst y₁
  subst y₂
  rcases maximalHorizontalLightSegment_endpoints gamma L.ell_pos hmax with
    hforward | hreverse
  · rcases hforward with ⟨rfl, rfl⟩
    rfl
  · rcases hreverse with ⟨rfl, rfl⟩
    exact closedSegment_comm _ _

/-- Unconditional uniqueness of the maximally extended light ray for the
localized analytic ansatz: every such ray is the full horizontal diameter.
The interior rigidity input is discharged by the preceding one-dimensional
calculus argument. -/
theorem uniqueMaximalLightRay
    {P : Params} {gamma : ℝ → ℝ → ℝ} {U : Set Point}
    (L : CompactSquareLocalization P gamma U)
    (hanalytic : AnalyticOnNhd ℝ (uncurried gamma) U)
    {a b : Point}
    (hmax : IsMaximallyExtendedLightSegment (openSquare L.ell)
      (fun w => ansatz gamma w.1 w.2) a b) :
    closedSegment a b = horizontalDiameter L.ell := by
  exact uniqueMaximalLightRay_of_interiorNormRigidity
    L hanalytic
      (lightSegmentInteriorNormRigidity_localizedAnsatz L hanalytic) hmax

end

end StressTensor
