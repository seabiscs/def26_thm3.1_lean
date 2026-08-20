import StressTensor.CKFirstOrderConvergence
import StressTensor.CKSmallParameter

/-!
# Normalized Nagumo majorant for the reduced nonlinear residual

This module estimates the sum of the positive-degree principal action and
the source composition at the normalized Nagumo scale

`phi(k) = 1 / (k+1)^2`.

The principal constant coefficient is removed before applying the formal
matrix action.  Consequently its convolution with an Euler-type state bound
is genuinely quadratic in the small amplitude.  The proof is independent of
the symmetric bivariate realization layer.
-/

namespace StressTensor
namespace CKNormalizedResidualMajorant

open CKFirstOrderFormalSystem CKFirstOrderConvergence
  CKFMSNagumoComposition CKNagumoMajorant CKSmallParameter

noncomputable section

/-- The normalized scalar profile used throughout this module. -/
abbrev normalizedNagumoProfile : ℕ → ℝ := nagumoCoeff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Nfun : FirstOrderPhase → FirstOrderOperator}
  {bfun : FirstOrderPhase → FirstOrderState}
  {center : FirstOrderPhase}

/-- Positive-degree part of the composed principal operator. -/
def normalizedPrincipalComposition
    (N : LocalAnalyticMajorant Nfun center)
    (p : FormalMultilinearSeries ℝ E FirstOrderPhase) :
    FormalMultilinearSeries ℝ E FirstOrderOperator :=
  N.series.comp p -
    constantOnly (E := E) (N.series 0).curry0

/-- The normalized nonlinear residual before polar extraction. -/
def normalizedResidual
    (N : LocalAnalyticMajorant Nfun center)
    (b : LocalAnalyticMajorant bfun center)
    (p : FormalMultilinearSeries ℝ E FirstOrderPhase)
    (e : FormalMultilinearSeries ℝ E FirstOrderState) :
    FormalMultilinearSeries ℝ E FirstOrderState :=
  formalActionOn (normalizedPrincipalComposition N p) e +
    b.series.comp p

/-- Principal positive-composition slope, with the small amplitude factored
out. -/
def principalNagumoSlope
    (N : LocalAnalyticMajorant Nfun center) (epsilon : ℝ) : ℝ :=
  nagumoCompositionSlope N.coefficientBound
    (N.radius : ℝ)⁻¹ epsilon

/-- Source positive-composition slope, with the small amplitude factored
out. -/
def sourceNagumoSlope
    (b : LocalAnalyticMajorant bfun center) (epsilon : ℝ) : ℝ :=
  nagumoCompositionSlope b.coefficientBound
    (b.radius : ℝ)⁻¹ epsilon

@[simp] theorem normalizedPrincipalComposition_zero
    (N : LocalAnalyticMajorant Nfun center)
    (p : FormalMultilinearSeries ℝ E FirstOrderPhase) :
    normalizedPrincipalComposition N p 0 = 0 := by
  rw [normalizedPrincipalComposition,
    comp_sub_constantOnly_eq_removeZero]
  rfl

theorem principalNagumoSlope_nonneg
    (N : LocalAnalyticMajorant Nfun center)
    {epsilon : ℝ}
    (hsmall : 8 * (epsilon * (N.radius : ℝ)⁻¹) < 1) :
    0 ≤ principalNagumoSlope N epsilon := by
  exact CKSmallParameter.nagumoCompositionSlope_nonneg
    N.coefficientBound_pos.le
    (inv_nonneg.mpr N.radius_real_pos.le) hsmall

theorem sourceNagumoSlope_nonneg
    (b : LocalAnalyticMajorant bfun center)
    {epsilon : ℝ}
    (hsmall : 8 * (epsilon * (b.radius : ℝ)⁻¹) < 1) :
    0 ≤ sourceNagumoSlope b epsilon := by
  exact CKSmallParameter.nagumoCompositionSlope_nonneg
    b.coefficientBound_pos.le
    (inv_nonneg.mpr b.radius_real_pos.le) hsmall

/-- Uniform bound for the positive-degree principal composition.  Its zero
coefficient vanishes exactly. -/
theorem norm_normalizedPrincipalComposition_le
    (N : LocalAnalyticMajorant Nfun center)
    {p : FormalMultilinearSeries ℝ E FirstOrderPhase}
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hsmall : 8 * (epsilon * (N.radius : ℝ)⁻¹) < 1)
    (hp0 : p 0 = 0)
    (hp : ∀ k, 0 < k →
      ‖p k‖ ≤ epsilon * normalizedNagumoProfile k) :
    ∀ k,
      ‖normalizedPrincipalComposition N p k‖ ≤
        principalNagumoSlope N epsilon * epsilon *
          normalizedNagumoProfile k := by
  intro k
  cases k with
  | zero =>
      rw [normalizedPrincipalComposition_zero, norm_zero]
      exact mul_nonneg
        (mul_nonneg (principalNagumoSlope_nonneg N hsmall) hepsilon)
        (nagumoCoeff_nonneg 0)
  | succ k =>
      have hcomp :=
        norm_comp_sub_constantOnly_le_nagumo
          N.coefficientBound_pos.le
          (inv_nonneg.mpr N.radius_real_pos.le)
          hepsilon (by norm_num : (0 : ℝ) ≤ 1) hsmall
          (q := N.series) (p := p)
          (fun l => by
            calc
              ‖N.series l‖ ≤
                  N.coefficientBound / (N.radius : ℝ) ^ l :=
                N.coeff_norm_le l
              _ = N.coefficientBound *
                    ((N.radius : ℝ)⁻¹) ^ l := by
                rw [inv_pow]
                ring)
          hp0 (fun j hj => by simpa using hp j hj)
          (n := k + 1) (by positivity)
      change
        ‖(N.series.comp p -
            constantOnly (E := E) (N.series 0).curry0) (k + 1)‖ ≤
          principalNagumoSlope N epsilon * epsilon *
            normalizedNagumoProfile (k + 1)
      calc
        ‖(N.series.comp p -
            constantOnly (E := E) (N.series 0).curry0) (k + 1)‖ ≤
            N.coefficientBound *
              ((epsilon * (N.radius : ℝ)⁻¹) /
                (1 - 8 * (epsilon * (N.radius : ℝ)⁻¹))) *
              normalizedNagumoProfile (k + 1) * 1 ^ (k + 1) := hcomp
        _ = principalNagumoSlope N epsilon * epsilon *
              normalizedNagumoProfile (k + 1) := by
          unfold principalNagumoSlope nagumoCompositionSlope
          ring

/-- Uniform source-composition estimate, including its constant coefficient. -/
theorem norm_sourceComposition_le
    (b : LocalAnalyticMajorant bfun center)
    {p : FormalMultilinearSeries ℝ E FirstOrderPhase}
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hsmall : 8 * (epsilon * (b.radius : ℝ)⁻¹) < 1)
    (hp0 : p 0 = 0)
    (hp : ∀ k, 0 < k →
      ‖p k‖ ≤ epsilon * normalizedNagumoProfile k) :
    ∀ k,
      ‖b.series.comp p k‖ ≤
        (if k = 0 then b.coefficientBound else 0) +
          sourceNagumoSlope b epsilon * epsilon *
            normalizedNagumoProfile k := by
  intro k
  cases k with
  | zero =>
      have hzero : ‖b.series.comp p 0‖ ≤ b.coefficientBound := by
        calc
          ‖b.series.comp p 0‖ =
              ‖b.series.comp p 0 (fun _ : Fin 0 => (0 : E))‖ := by
            exact (ContinuousMultilinearMap.fin0_apply_norm
              (b.series.comp p 0)).symm
          _ = ‖b.series 0 (fun _ : Fin 0 => (0 : FirstOrderPhase))‖ := by
            rw [FormalMultilinearSeries.comp_coeff_zero]
          _ = ‖b.series 0‖ := by
            exact ContinuousMultilinearMap.fin0_apply_norm (b.series 0)
          _ ≤ b.coefficientBound / (b.radius : ℝ) ^ 0 :=
            b.coeff_norm_le 0
          _ = b.coefficientBound := by simp
      simp only [ite_true]
      exact hzero.trans (le_add_of_nonneg_right
        (mul_nonneg
          (mul_nonneg (sourceNagumoSlope_nonneg b hsmall) hepsilon)
          (nagumoCoeff_nonneg 0)))
  | succ k =>
      have hcomp :=
        CKFMSNagumoComposition.LocalAnalyticMajorant.norm_comp_le_nagumo
          b hepsilon (by norm_num : (0 : ℝ) ≤ 1) hsmall hp0
          (fun j hj => by simpa using hp j hj)
          (n := k + 1) (by positivity)
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false,
        zero_add]
      calc
        ‖b.series.comp p (k + 1)‖ ≤
            b.coefficientBound *
              ((epsilon * (b.radius : ℝ)⁻¹) /
                (1 - 8 * (epsilon * (b.radius : ℝ)⁻¹))) *
              normalizedNagumoProfile (k + 1) * 1 ^ (k + 1) := hcomp
        _ = sourceNagumoSlope b epsilon * epsilon *
              normalizedNagumoProfile (k + 1) := by
          unfold sourceNagumoSlope nagumoCompositionSlope
          ring

/-- The positive principal action is quadratic in the normalized small
amplitude.  The constant `32` is `2` from the two-component matrix action
times `16` from the weighted Nagumo convolution. -/
theorem norm_normalizedPrincipalAction_le
    (N : LocalAnalyticMajorant Nfun center)
    {p : FormalMultilinearSeries ℝ E FirstOrderPhase}
    {e : FormalMultilinearSeries ℝ E FirstOrderState}
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hsmall : 8 * (epsilon * (N.radius : ℝ)⁻¹) < 1)
    (hp0 : p 0 = 0)
    (hp : ∀ k, 0 < k →
      ‖p k‖ ≤ epsilon * normalizedNagumoProfile k)
    (he : ∀ k,
      ‖e k‖ ≤ epsilon * (k : ℝ) * normalizedNagumoProfile k) :
    ∀ k,
      ‖formalActionOn (normalizedPrincipalComposition N p) e k‖ ≤
        32 * principalNagumoSlope N epsilon * epsilon ^ 2 *
          (k + 1 : ℝ) * normalizedNagumoProfile (k + 1) := by
  intro k
  let Cn := principalNagumoSlope N epsilon
  have hCn : 0 ≤ Cn := principalNagumoSlope_nonneg N hsmall
  have hprincipal := norm_normalizedPrincipalComposition_le
    N hepsilon hsmall hp0 hp
  calc
    ‖formalActionOn (normalizedPrincipalComposition N p) e k‖ ≤
        ∑ i ∈ Finset.range (k + 1),
          2 * ‖normalizedPrincipalComposition N p i‖ * ‖e (k - i)‖ :=
      norm_formalActionOn_le _ _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1),
          2 * (Cn * epsilon * normalizedNagumoProfile i) *
            (epsilon * ((k - i : ℕ) : ℝ) *
              normalizedNagumoProfile (k - i)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hprincipal i) (by norm_num))
        (he (k - i)) (norm_nonneg _)
        (mul_nonneg (by norm_num)
          (mul_nonneg
            (mul_nonneg hCn hepsilon)
            (nagumoCoeff_nonneg i)))
    _ = 2 * Cn * epsilon ^ 2 *
          (∑ ij ∈ Finset.antidiagonal k,
            normalizedNagumoProfile ij.1 * (ij.2 : ℝ) *
              normalizedNagumoProfile ij.2) := by
      calc
        ∑ i ∈ Finset.range (k + 1),
            2 * (Cn * epsilon * normalizedNagumoProfile i) *
              (epsilon * ((k - i : ℕ) : ℝ) *
                normalizedNagumoProfile (k - i)) =
            ∑ ij ∈ Finset.antidiagonal k,
              2 * (Cn * epsilon * normalizedNagumoProfile ij.1) *
                (epsilon * (ij.2 : ℝ) *
                  normalizedNagumoProfile ij.2) := by
          simpa using
            (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j =>
                2 * (Cn * epsilon * normalizedNagumoProfile i) *
                  (epsilon * (j : ℝ) * normalizedNagumoProfile j)) k).symm
        _ = ∑ ij ∈ Finset.antidiagonal k,
              (2 * Cn * epsilon ^ 2) *
                (normalizedNagumoProfile ij.1 * (ij.2 : ℝ) *
                  normalizedNagumoProfile ij.2) := by
          apply Finset.sum_congr rfl
          intro ij hij
          ring
        _ = 2 * Cn * epsilon ^ 2 *
            (∑ ij ∈ Finset.antidiagonal k,
              normalizedNagumoProfile ij.1 * (ij.2 : ℝ) *
                normalizedNagumoProfile ij.2) := by
          rw [Finset.mul_sum]
    _ ≤ 2 * Cn * epsilon ^ 2 *
          (16 * (k + 1 : ℝ) * normalizedNagumoProfile (k + 1)) := by
      gcongr
      exact weightedDerivativeConvolution_nagumoCoeff_le k
    _ = 32 * principalNagumoSlope N epsilon * epsilon ^ 2 *
          (k + 1 : ℝ) * normalizedNagumoProfile (k + 1) := by
      dsimp [Cn]
      ring

/-- Complete normalized residual estimate. -/
theorem norm_normalizedResidual_le
    (N : LocalAnalyticMajorant Nfun center)
    (b : LocalAnalyticMajorant bfun center)
    {p : FormalMultilinearSeries ℝ E FirstOrderPhase}
    {e : FormalMultilinearSeries ℝ E FirstOrderState}
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hsmallN : 8 * (epsilon * (N.radius : ℝ)⁻¹) < 1)
    (hsmallb : 8 * (epsilon * (b.radius : ℝ)⁻¹) < 1)
    (hp0 : p 0 = 0)
    (hp : ∀ k, 0 < k →
      ‖p k‖ ≤ epsilon * normalizedNagumoProfile k)
    (he : ∀ k,
      ‖e k‖ ≤ epsilon * (k : ℝ) * normalizedNagumoProfile k) :
    ∀ k,
      ‖normalizedResidual N b p e k‖ ≤
        (if k = 0 then b.coefficientBound else 0) +
          sourceNagumoSlope b epsilon * epsilon *
            normalizedNagumoProfile k +
          32 * principalNagumoSlope N epsilon * epsilon ^ 2 *
            (k + 1 : ℝ) * normalizedNagumoProfile (k + 1) := by
  intro k
  have haction := norm_normalizedPrincipalAction_le
    N hepsilon hsmallN hp0 hp he k
  have hsource := norm_sourceComposition_le
    b hepsilon hsmallb hp0 hp k
  unfold normalizedResidual
  calc
    ‖(formalActionOn (normalizedPrincipalComposition N p) e +
        b.series.comp p) k‖ ≤
        ‖formalActionOn (normalizedPrincipalComposition N p) e k‖ +
          ‖b.series.comp p k‖ := by
      change
        ‖formalActionOn (normalizedPrincipalComposition N p) e k +
            b.series.comp p k‖ ≤ _
      exact norm_add_le _ _
    _ ≤
        32 * principalNagumoSlope N epsilon * epsilon ^ 2 *
            (k + 1 : ℝ) * normalizedNagumoProfile (k + 1) +
          ((if k = 0 then b.coefficientBound else 0) +
            sourceNagumoSlope b epsilon * epsilon *
              normalizedNagumoProfile k) :=
      add_le_add haction hsource
    _ =
        (if k = 0 then b.coefficientBound else 0) +
          sourceNagumoSlope b epsilon * epsilon *
            normalizedNagumoProfile k +
          32 * principalNagumoSlope N epsilon * epsilon ^ 2 *
            (k + 1 : ℝ) * normalizedNagumoProfile (k + 1) := by
      ring

end

end CKNormalizedResidualMajorant
end StressTensor
