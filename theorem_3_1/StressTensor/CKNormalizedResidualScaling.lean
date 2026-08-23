import StressTensor.CKNormalizedResidualMajorant
import StressTensor.CKNormalizedPhase
import StressTensor.CKFormalDiagonalCongruence
import StressTensor.CKPolarScaling
import StressTensor.CKFormalRecurrenceDiagonalIdentity

/-!
# Scaling normalized nonlinear residuals back to bivariate coefficients

This file supplies the representation-independent scaling bridge used by
the zero-origin Nagumo induction.  Its first part is generic: a normalized
residual on any real normed input space is compared on diagonals with the
physical two-variable residual, and polar scaling restores exactly the
factor `R^m S^n`.
-/

namespace StressTensor
namespace CKNormalizedResidualScaling

open CKFirstOrderFormalSystem CKFirstOrderConvergence
  CKFormalDiagonalCongruence CKPolarUniqueness CKPolarScaling
  CKNormalizedResidualMajorant CKFMSNagumoComposition
  CKNormalizedPhase CKBivariateRateNormalization
  CKSymmetricBivariateFMS CKFuchsianMajorant CKSmallParameter

noncomputable section

/-! ## Heterogeneous diagonal congruence -/

/-- Equality of all state-valued diagonal homogeneous evaluations implies
equality of all project polar coefficients. -/
theorem polarCoefficient_eq_of_apply_diag_eq
    (p q : StateSeries)
    (hdiag : ∀ k z,
      p k (fun _ : Fin k => z) = q k (fun _ : Fin k => z))
    (m n : ℕ) :
    CKPolarEvaluation.polarCoefficient p m n =
      CKPolarEvaluation.polarCoefficient q m n := by
  have hzero :=
    CKPolarUniqueness.state_polarCoefficient_eq_zero_of_apply_diag_eq_zero
      (p - q) (fun k z => by
        change p k (fun _ : Fin k => z) - q k (fun _ : Fin k => z) = 0
        rw [hdiag k z, sub_self]) m n
  rw [CKPolarUniqueness.polarCoefficient_sub, sub_eq_zero] at hzero
  exact hzero

/-- Formal composition can compare diagonal inputs living in two different
normed domains. -/
theorem comp_apply_diag_congr_inner_heterogeneous
    {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (q : FormalMultilinearSeries ℝ G H)
    (p : FormalMultilinearSeries ℝ E G)
    (r : FormalMultilinearSeries ℝ F G)
    (z : E) (w : F)
    (hpr : ∀ d,
      p d (fun _ : Fin d => z) = r d (fun _ : Fin d => w))
    (k : ℕ) :
    q.comp p k (fun _ : Fin k => z) =
      q.comp r k (fun _ : Fin k => w) := by
  unfold FormalMultilinearSeries.comp
  rw [sum_apply, sum_apply]
  apply Finset.sum_congr rfl
  intro c hc
  simp only [FormalMultilinearSeries.compAlongComposition_apply]
  congr 1
  funext i
  unfold FormalMultilinearSeries.applyComposition
  have hz :
      ((fun _ : Fin k => z) ∘ c.embedding i) =
        (fun _ : Fin (c.blocksFun i) => z) := by
    funext j
    rfl
  have hw :
      ((fun _ : Fin k => w) ∘ c.embedding i) =
        (fun _ : Fin (c.blocksFun i) => w) := by
    funext j
    rfl
  rw [hz, hw, hpr]

/-- Generic formal matrix action can likewise compare diagonal inputs in
different normed domains. -/
theorem formalActionOn_apply_diag_congr_heterogeneous
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : FormalMultilinearSeries ℝ E FirstOrderOperator)
    (B : FormalMultilinearSeries ℝ F FirstOrderOperator)
    (u : FormalMultilinearSeries ℝ E FirstOrderState)
    (v : FormalMultilinearSeries ℝ F FirstOrderState)
    (z : E) (w : F)
    (hA : ∀ d,
      A d (fun _ : Fin d => z) = B d (fun _ : Fin d => w))
    (hu : ∀ d,
      u d (fun _ : Fin d => z) = v d (fun _ : Fin d => w))
    (k : ℕ) :
    formalActionOn A u k (fun _ : Fin k => z) =
      formalActionOn B v k (fun _ : Fin k => w) := by
  rw [CKFormalDiagonalCongruence.formalActionOn_apply_diag,
    CKFormalDiagonalCongruence.formalActionOn_apply_diag]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hA i, hu (k - i)]

/-! ## The normalized residual respects heterogeneous diagonal data -/

variable {Nfun : FirstOrderPhase → FirstOrderOperator}
  {bfun : FirstOrderPhase → FirstOrderState}
  {center : FirstOrderPhase}

theorem normalizedPrincipalComposition_apply_diag_congr_heterogeneous
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (N : LocalAnalyticMajorant Nfun center)
    (p : FormalMultilinearSeries ℝ E FirstOrderPhase)
    (r : FormalMultilinearSeries ℝ F FirstOrderPhase)
    (z : E) (w : F)
    (hpr : ∀ d,
      p d (fun _ : Fin d => z) = r d (fun _ : Fin d => w))
    (k : ℕ) :
    normalizedPrincipalComposition N p k (fun _ : Fin k => z) =
      normalizedPrincipalComposition N r k (fun _ : Fin k => w) := by
  unfold normalizedPrincipalComposition
  change
    N.series.comp p k (fun _ : Fin k => z) -
        constantOnly (E := E) (N.series 0).curry0 k
          (fun _ : Fin k => z) =
      N.series.comp r k (fun _ : Fin k => w) -
        constantOnly (E := F) (N.series 0).curry0 k
          (fun _ : Fin k => w)
  rw [comp_apply_diag_congr_inner_heterogeneous N.series p r z w hpr k]
  congr 1
  cases k <;> simp [constantOnly]

theorem normalizedResidual_apply_diag_congr_heterogeneous
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (N : LocalAnalyticMajorant Nfun center)
    (b : LocalAnalyticMajorant bfun center)
    (p : FormalMultilinearSeries ℝ E FirstOrderPhase)
    (r : FormalMultilinearSeries ℝ F FirstOrderPhase)
    (e : FormalMultilinearSeries ℝ E FirstOrderState)
    (f : FormalMultilinearSeries ℝ F FirstOrderState)
    (z : E) (w : F)
    (hpr : ∀ d,
      p d (fun _ : Fin d => z) = r d (fun _ : Fin d => w))
    (hef : ∀ d,
      e d (fun _ : Fin d => z) = f d (fun _ : Fin d => w))
    (k : ℕ) :
    normalizedResidual N b p e k (fun _ : Fin k => z) =
      normalizedResidual N b r f k (fun _ : Fin k => w) := by
  unfold normalizedResidual
  change
    formalActionOn (normalizedPrincipalComposition N p) e k
          (fun _ : Fin k => z) +
        b.series.comp p k (fun _ : Fin k => z) =
      formalActionOn (normalizedPrincipalComposition N r) f k
          (fun _ : Fin k => w) +
        b.series.comp r k (fun _ : Fin k => w)
  rw [formalActionOn_apply_diag_congr_heterogeneous
      (normalizedPrincipalComposition N p)
      (normalizedPrincipalComposition N r) e f z w
      (normalizedPrincipalComposition_apply_diag_congr_heterogeneous
        N p r z w hpr) hef k,
    comp_apply_diag_congr_inner_heterogeneous b.series p r z w hpr k]

/-- Adding back the constant principal action recovers the full composed
principal action, on every diagonal homogeneous evaluation. -/
theorem normalizedResidual_add_constant_apply_diag
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : LocalAnalyticMajorant Nfun center)
    (b : LocalAnalyticMajorant bfun center)
    (p : FormalMultilinearSeries ℝ E FirstOrderPhase)
    (e : FormalMultilinearSeries ℝ E FirstOrderState)
    (k : ℕ) (z : E) :
    normalizedResidual N b p e k (fun _ : Fin k => z) +
        formalActionOn
          (constantOnly (E := E) (N.series 0).curry0) e k
          (fun _ : Fin k => z) =
      (formalActionOn (N.series.comp p) e + b.series.comp p) k
        (fun _ : Fin k => z) := by
  unfold normalizedResidual normalizedPrincipalComposition
  change
    formalActionOn
          (N.series.comp p -
            constantOnly (E := E) (N.series 0).curry0) e k
          (fun _ : Fin k => z) +
        b.series.comp p k (fun _ : Fin k => z) +
        formalActionOn
          (constantOnly (E := E) (N.series 0).curry0) e k
          (fun _ : Fin k => z) =
      formalActionOn (N.series.comp p) e k (fun _ : Fin k => z) +
        b.series.comp p k (fun _ : Fin k => z)
  rw [CKFormalDiagonalCongruence.formalActionOn_apply_diag,
    CKFormalDiagonalCongruence.formalActionOn_apply_diag,
    CKFormalDiagonalCongruence.formalActionOn_apply_diag]
  simp only [FormalMultilinearSeries.sub_apply, sub_apply, map_sub,
    Finset.sum_sub_distrib]
  abel

theorem constantOnly_eq_constFormalMultilinearSeries
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : G) :
    constantOnly (E := E) g =
      constFormalMultilinearSeries ℝ E g := by
  apply FormalMultilinearSeries.ext
  intro k
  cases k <;> rfl

/-! ## Identification with the equation-specific residual -/

/-- The physical positive-principal-plus-source formal series whose polar
coefficients are `firstOrderNonlinearResidual`. -/
def firstOrderNonlinearResidualFMS
    (P : Params) (a : BivariateStateCoeff) : StateSeries :=
  normalizedResidual
    (firstOrderPrincipalOriginMajorant P)
    (firstOrderSourceOriginMajorant P)
    (phaseSeries (stateBivariateFMS a))
    (formalEulerY (stateBivariateFMS a))

theorem firstOrderPrincipalOriginMajorant_curry0
    (P : Params) :
    ((firstOrderPrincipalOriginMajorant P).series 0).curry0 =
      firstOrderPrincipalArray P firstOrderOrigin := by
  rw [ContinuousMultilinearMap.curry0_apply]
  have hinput : (0 : Fin 0 → FirstOrderPhase) = ![] :=
    Subsingleton.elim _ _
  rw [hinput]
  exact firstOrderPrincipalOriginMajorant_zero P ![]

/-- Exact coefficient identification of the physical nonlinear residual. -/
theorem polarCoefficient_firstOrderNonlinearResidualFMS
    (P : Params) (a : BivariateStateCoeff) (m n : ℕ) :
    CKPolarEvaluation.polarCoefficient
        (firstOrderNonlinearResidualFMS P a) m n =
      firstOrderNonlinearResidual P a m n := by
  let N := firstOrderPrincipalOriginMajorant P
  let b := firstOrderSourceOriginMajorant P
  let U := stateBivariateFMS a
  let e := formalEulerY U
  let C : OperatorSeries :=
    constFormalMultilinearSeries ℝ Domain (N.series 0).curry0
  have hdiag : ∀ k z,
      firstOrderNonlinearResidualFMS P a k (fun _ : Fin k => z) =
        (reducedRHS N.series b.series U - formalAction C e) k
          (fun _ : Fin k => z) := by
    intro k z
    have hsum := normalizedResidual_add_constant_apply_diag
      N b (phaseSeries U) e k z
    rw [constantOnly_eq_constFormalMultilinearSeries] at hsum
    change
      firstOrderNonlinearResidualFMS P a k (fun _ : Fin k => z) =
        reducedRHS N.series b.series U k (fun _ : Fin k => z) -
          formalAction C e k (fun _ : Fin k => z)
    exact eq_sub_of_add_eq hsum
  have hpolar := polarCoefficient_eq_of_apply_diag_eq
    (firstOrderNonlinearResidualFMS P a)
    (reducedRHS N.series b.series U - formalAction C e)
    hdiag m n
  rw [CKPolarUniqueness.polarCoefficient_sub] at hpolar
  calc
    CKPolarEvaluation.polarCoefficient
        (firstOrderNonlinearResidualFMS P a) m n =
        CKPolarEvaluation.polarCoefficient
            (reducedRHS N.series b.series U) m n -
          CKPolarEvaluation.polarCoefficient (formalAction C e) m n := hpolar
    _ = reducedArrayRHS N.series b.series a m n -
          (n : ℝ) • Matrix.mulVec (N.series 0).curry0 (a m n) := by
      rw [show CKPolarEvaluation.polarCoefficient
            (reducedRHS N.series b.series U) m n =
          reducedArrayRHS N.series b.series a m n by rfl]
      exact congrArg
        (fun v : FirstOrderState =>
          reducedArrayRHS N.series b.series a m n - v)
        (polarCoefficient_formalAction_const_formalEulerY_stateBivariateFMS
          (N.series 0).curry0 a m n)
    _ = firstOrderNonlinearResidual P a m n := by
      dsimp [N, b]
      rw [firstOrderPrincipalOriginMajorant_zero P
        (0 : Fin 0 → FirstOrderPhase)]
      rfl

/-! ## Exact polar rate restoration -/

/-- If a physical residual is diagonally the pullback of a normalized
residual, polar extraction restores the two rates exactly. -/
theorem polarCoefficient_eq_rate_smul_polarCoefficientAlong
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (physical : StateSeries)
    (normalized : FormalMultilinearSeries ℝ E FirstOrderState)
    (L : Domain →L[ℝ] E) (ex ey : E) (R S : ℝ)
    (hdiag : ∀ k z,
      physical k (fun _ : Fin k => z) =
        normalized.compContinuousLinearMap L k
          (fun _ : Fin k => z))
    (hLx : L (1, 0) = R • ex)
    (hLy : L (0, 1) = S • ey)
    (m n : ℕ) :
    CKPolarEvaluation.polarCoefficient physical m n =
      (R ^ m * S ^ n) •
        polarCoefficientAlong normalized ex ey m n := by
  calc
    CKPolarEvaluation.polarCoefficient physical m n =
        CKPolarEvaluation.polarCoefficient
          (normalized.compContinuousLinearMap L) m n :=
      polarCoefficient_eq_of_apply_diag_eq physical
        (normalized.compContinuousLinearMap L) hdiag m n
    _ = polarCoefficientAlong
          (normalized.compContinuousLinearMap L) (1, 0) (0, 1) m n :=
      (polarCoefficientAlong_coordinateDirections
        (normalized.compContinuousLinearMap L) m n).symm
    _ = polarCoefficientAlong normalized (L (1, 0)) (L (0, 1)) m n :=
      polarCoefficientAlong_compContinuousLinearMap
        normalized L (1, 0) (0, 1) m n
    _ = polarCoefficientAlong normalized (R • ex) (S • ey) m n := by
      rw [hLx, hLy]
    _ = (R ^ m * S ^ n) •
          polarCoefficientAlong normalized ex ey m n :=
      polarCoefficientAlong_smul_directions normalized ex ey R S m n

/-- Norm form of exact polar rate restoration. -/
theorem norm_polarCoefficient_le_diagonalTransportEnvelope
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (physical : StateSeries)
    (normalized : FormalMultilinearSeries ℝ E FirstOrderState)
    (L : Domain →L[ℝ] E) (ex ey : E)
    {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (hdiag : ∀ k z,
      physical k (fun _ : Fin k => z) =
        normalized.compContinuousLinearMap L k
          (fun _ : Fin k => z))
    (hLx : L (1, 0) = R • ex)
    (hLy : L (0, 1) = S • ey)
    (hex : ‖ex‖ ≤ 1) (hey : ‖ey‖ ≤ 1)
    (g : ℕ → ℝ)
    (hnormalized : ∀ k, ‖normalized k‖ ≤ g k)
    (m n : ℕ) :
    ‖CKPolarEvaluation.polarCoefficient physical m n‖ ≤
      diagonalTransportEnvelope g R S m n := by
  rw [polarCoefficient_eq_rate_smul_polarCoefficientAlong
    physical normalized L ex ey R S hdiag hLx hLy]
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (mul_pos (pow_pos hR m) (pow_pos hS n))]
  calc
    (R ^ m * S ^ n) *
        ‖polarCoefficientAlong normalized ex ey m n‖ ≤
      (R ^ m * S ^ n) *
        (((m + n).choose m : ℝ) * ‖normalized (m + n)‖) := by
      exact mul_le_mul_of_nonneg_left
        (norm_polarCoefficientAlong_le normalized ex ey hex hey m n)
        (mul_nonneg (pow_nonneg hR.le m) (pow_nonneg hS.le n))
    _ ≤ (R ^ m * S ^ n) *
        (((m + n).choose m : ℝ) * g (m + n)) := by
      gcongr
      exact hnormalized (m + n)
    _ = diagonalTransportEnvelope g R S m n := by
      unfold diagonalTransportEnvelope
      ring

/-! ## The equation-specific normalized residual -/

/-- Unit evolution direction in the `L¹` product domain. -/
def normalizedXDirection : L1Domain :=
  WithLp.toLp 1 ((1 : ℝ), (0 : ℝ))

/-- Unit tangential direction in the `L¹` product domain. -/
def normalizedYDirection : L1Domain :=
  WithLp.toLp 1 ((0 : ℝ), (1 : ℝ))

@[simp] theorem norm_normalizedXDirection :
    ‖normalizedXDirection‖ = 1 := by
  rw [WithLp.prod_norm_eq_of_L1 normalizedXDirection]
  norm_num [normalizedXDirection]

@[simp] theorem norm_normalizedYDirection :
    ‖normalizedYDirection‖ = 1 := by
  rw [WithLp.prod_norm_eq_of_L1 normalizedYDirection]
  norm_num [normalizedYDirection]

@[simp] theorem weightedDomainMap_xDirection (R S : ℝ) :
    weightedDomainMap R S (1, 0) = R • normalizedXDirection := by
  rw [weightedDomainMap_apply, normalizedXDirection,
    ← WithLp.toLp_smul]
  congr 1
  ext <;> simp

@[simp] theorem weightedDomainMap_yDirection (R S : ℝ) :
    weightedDomainMap R S (0, 1) = S • normalizedYDirection := by
  rw [weightedDomainMap_apply, normalizedYDirection,
    ← WithLp.toLp_smul]
  congr 1
  ext <;> simp

/-- Residual formed from the rate-normalized phase and Euler series. -/
def normalizedFirstOrderResidual
    (P : Params) (R S : ℝ) (a : BivariateStateCoeff) :
    FormalMultilinearSeries ℝ L1Domain FirstOrderState :=
  normalizedResidual
    (firstOrderPrincipalOriginMajorant P)
    (firstOrderSourceOriginMajorant P)
    (normalizedPhaseFMS S (normalizeStateCoeff R S a))
    (normalizedEulerFMS (normalizeStateCoeff R S a))

/-- Pulling the normalized residual back by the weighted domain map restores
the physical residual on every homogeneous diagonal. -/
theorem firstOrderNonlinearResidualFMS_comp_weightedDomainMap_apply_diag
    {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (P : Params) (a : BivariateStateCoeff) (k : ℕ) (x y : ℝ) :
    firstOrderNonlinearResidualFMS P a k
        (fun _ : Fin k => (x, y)) =
      (normalizedFirstOrderResidual P R S a).compContinuousLinearMap
          (weightedDomainMap R S) k (fun _ : Fin k => (x, y)) := by
  rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
  symm
  apply normalizedResidual_apply_diag_congr_heterogeneous
    (firstOrderPrincipalOriginMajorant P)
    (firstOrderSourceOriginMajorant P)
    (normalizedPhaseFMS S (normalizeStateCoeff R S a))
    (phaseSeries (stateBivariateFMS a))
    (normalizedEulerFMS (normalizeStateCoeff R S a))
    (formalEulerY (stateBivariateFMS a))
    (weightedDomainMap R S (x, y)) (x, y)
  · intro d
    have h := normalizedPhaseFMS_comp_weightedDomainMap_apply_diag
      hR hS a d x y
    rw [FormalMultilinearSeries.compContinuousLinearMap_apply] at h
    convert h using 1
    all_goals rfl
  · intro d
    have h := normalizedEulerFMS_comp_weightedDomainMap_apply_diag
      hR hS a d x y
    rw [FormalMultilinearSeries.compContinuousLinearMap_apply] at h
    convert h using 1
    all_goals rfl

/-- Exact coefficient scaling from the normalized residual back to the
physical nonlinear residual. -/
theorem firstOrderNonlinearResidual_eq_rate_smul_normalizedPolar
    {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (P : Params) (a : BivariateStateCoeff) (m n : ℕ) :
    firstOrderNonlinearResidual P a m n =
      (R ^ m * S ^ n) •
        polarCoefficientAlong (normalizedFirstOrderResidual P R S a)
          normalizedXDirection normalizedYDirection m n := by
  rw [← polarCoefficient_firstOrderNonlinearResidualFMS P a m n]
  exact polarCoefficient_eq_rate_smul_polarCoefficientAlong
    (firstOrderNonlinearResidualFMS P a)
    (normalizedFirstOrderResidual P R S a)
    (weightedDomainMap R S) normalizedXDirection normalizedYDirection R S
    (fun k z => by
      exact firstOrderNonlinearResidualFMS_comp_weightedDomainMap_apply_diag
        hR hS P a k z.1 z.2)
    (weightedDomainMap_xDirection R S)
    (weightedDomainMap_yDirection R S) m n

/-! ## The transported residual envelope -/

/-- The scalar Nagumo profile produced by the complete normalized residual
estimate: the source constant term, the positive source composition, and
the quadratic positive-principal action. -/
def firstOrderResidualNagumoProfile (P : Params) (epsilon : ℝ) (k : ℕ) : ℝ :=
  (if k = 0 then
      (firstOrderSourceOriginMajorant P).coefficientBound
    else 0) +
    sourceNagumoSlope (firstOrderSourceOriginMajorant P) epsilon * epsilon *
      normalizedNagumoProfile k +
    32 * principalNagumoSlope
        (firstOrderPrincipalOriginMajorant P) epsilon * epsilon ^ 2 *
      (k + 1 : ℝ) * normalizedNagumoProfile (k + 1)

/-- Final scaling estimate used by the zero-origin causal induction.

If the physical coefficients lie below the transported Nagumo profile and
the normalized linear `y` coordinate also fits that profile, then every
physical nonlinear residual coefficient lies below the transported complete
residual profile. -/
theorem norm_firstOrderNonlinearResidual_le_diagonalTransportEnvelope
    (P : Params) {R S epsilon : ℝ}
    (hR : 0 < R) (hS : 0 < S) (hepsilon : 0 ≤ epsilon)
    (hsmallN :
      8 * (epsilon *
        ((firstOrderPrincipalOriginMajorant P).radius : ℝ)⁻¹) < 1)
    (hsmallb :
      8 * (epsilon *
        ((firstOrderSourceOriginMajorant P).radius : ℝ)⁻¹) < 1)
    (hy : S⁻¹ ≤ epsilon * normalizedNagumoProfile 1)
    {a : BivariateStateCoeff} (ha00 : a 0 0 = 0)
    (ha : ∀ m n,
      ‖a m n‖ ≤ diagonalTransportEnvelope
        (fun k => epsilon * normalizedNagumoProfile k) R S m n)
    (m n : ℕ) :
    ‖firstOrderNonlinearResidual P a m n‖ ≤
      diagonalTransportEnvelope
        (firstOrderResidualNagumoProfile P epsilon) R S m n := by
  have hprofile : ∀ k, 0 ≤ epsilon * normalizedNagumoProfile k := by
    intro k
    exact mul_nonneg hepsilon (CKNagumoMajorant.nagumoCoeff_nonneg k)
  have haNormalized : ∀ i j,
      ‖normalizeStateCoeff R S a i j‖ ≤
        (((i + j).choose i : ℝ) *
          (epsilon * normalizedNagumoProfile (i + j))) :=
    norm_normalizeStateCoeff_le hR hS hprofile ha
  have hp0 :
      normalizedPhaseFMS S (normalizeStateCoeff R S a) 0 = 0 :=
    normalizedPhaseFMS_zero S
      (normalizeStateCoeff_zero R S ha00)
  have hp : ∀ k,
      ‖normalizedPhaseFMS S (normalizeStateCoeff R S a) k‖ ≤
        epsilon * normalizedNagumoProfile k := by
    intro k
    exact norm_normalizedPhaseFMS_le hS
      (normalizeStateCoeff R S a) epsilon normalizedNagumoProfile
      haNormalized hy k
  have he : ∀ k,
      ‖normalizedEulerFMS (normalizeStateCoeff R S a) k‖ ≤
        epsilon * (k : ℝ) * normalizedNagumoProfile k := by
    intro k
    exact norm_normalizedEulerFMS_le
      (normalizeStateCoeff R S a) epsilon normalizedNagumoProfile
      haNormalized k
  have hnormalized : ∀ k,
      ‖normalizedFirstOrderResidual P R S a k‖ ≤
        firstOrderResidualNagumoProfile P epsilon k := by
    intro k
    simpa only [normalizedFirstOrderResidual,
      firstOrderResidualNagumoProfile] using
      (norm_normalizedResidual_le
        (firstOrderPrincipalOriginMajorant P)
        (firstOrderSourceOriginMajorant P)
        hepsilon hsmallN hsmallb hp0
        (fun d _ => hp d) he k)
  have hscaled := norm_polarCoefficient_le_diagonalTransportEnvelope
    (firstOrderNonlinearResidualFMS P a)
    (normalizedFirstOrderResidual P R S a)
    (weightedDomainMap R S) normalizedXDirection normalizedYDirection
    hR hS
    (fun k z =>
      firstOrderNonlinearResidualFMS_comp_weightedDomainMap_apply_diag
        hR hS P a k z.1 z.2)
    (weightedDomainMap_xDirection R S)
    (weightedDomainMap_yDirection R S)
    (by simp) (by simp)
    (firstOrderResidualNagumoProfile P epsilon) hnormalized m n
  rw [polarCoefficient_firstOrderNonlinearResidualFMS] at hscaled
  exact hscaled

/-- Tangential-rate specialization: `S = 4 / epsilon` makes the normalized
linear `y` coefficient equal exactly to `epsilon * nagumoCoeff 1`. -/
theorem norm_firstOrderNonlinearResidual_le_diagonalTransportEnvelope_tangentialRate
    (P : Params) {R epsilon : ℝ}
    (hR : 0 < R) (hepsilon : 0 < epsilon)
    (hsmallN :
      8 * (epsilon *
        ((firstOrderPrincipalOriginMajorant P).radius : ℝ)⁻¹) < 1)
    (hsmallb :
      8 * (epsilon *
        ((firstOrderSourceOriginMajorant P).radius : ℝ)⁻¹) < 1)
    {a : BivariateStateCoeff} (ha00 : a 0 0 = 0)
    (ha : ∀ m n,
      ‖a m n‖ ≤ diagonalTransportEnvelope
        (fun k => epsilon * normalizedNagumoProfile k)
        R (tangentialRate epsilon) m n)
    (m n : ℕ) :
    ‖firstOrderNonlinearResidual P a m n‖ ≤
      diagonalTransportEnvelope
        (firstOrderResidualNagumoProfile P epsilon)
        R (tangentialRate epsilon) m n := by
  apply norm_firstOrderNonlinearResidual_le_diagonalTransportEnvelope
    P hR (tangentialRate_pos hepsilon) hepsilon.le
    hsmallN hsmallb
  · exact (inv_tangentialRate_eq_nagumo hepsilon).le
  · exact ha00
  · exact ha

end

end CKNormalizedResidualScaling
end StressTensor
