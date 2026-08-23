import StressTensor.CKFirstOrderFormalSystem
import StressTensor.CKFormalActionEvaluation
import StressTensor.CKPolarUniqueness
import StressTensor.CKBivariateConvolutionMajorant
import StressTensor.CKVectorAnalyticEvaluation
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Convergence interface for the reduced first-order stress system

This file connects the equation-specific formal recurrence for

`U_x = y N(y,U) U_y + b(y,U)`

to the generic Fuchsian/Catalan majorant machinery.  It proves three pieces
which do not depend on a choice of scalar majorant algebra:

* homogeneous geometric bounds for the analytic compositions with `N` and
  `b`, using the quantitative Taylor germs at the origin;
* the exact split of the coefficient recurrence into the constant-principal
  Euler transport `n N(0) a[m,n]` and a causal nonlinear residual; and
* a product-geometric convergence theorem conditional on one named bound for
  that residual.

Thus `HasFirstOrderResidualMajorant` is the precise remaining nonlinear
estimate.  No convergence assertion is hidden in the formal recursion.
-/

namespace StressTensor
namespace CKFirstOrderConvergence

open CKFirstOrderFormalSystem CKPowerSeries CKGeometricMajorant
  CKDiagonalMajorant CKFuchsianMajorant CKBivariateConvolutionMajorant
  CKFormalActionEvaluation CKPolarUniqueness

noncomputable section

/-! ## Polar coefficient bounds -/

lemma norm_polarSlotInput (k : ℕ) (s : Finset (Fin k)) (i : Fin k) :
    ‖polarSlotInput k s i‖ = 1 := by
  unfold polarSlotInput
  split_ifs <;> simp [Prod.norm_def]

/-- Polarization costs exactly the number of subsets of cardinality `m`. -/
lemma norm_polarCoefficient_le
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p : FormalMultilinearSeries ℝ Domain G) (m n : ℕ) :
    ‖polarCoefficient p m n‖ ≤
      ((m + n).choose m : ℝ) * ‖p (m + n)‖ := by
  unfold polarCoefficient
  calc
    ‖∑ s ∈ (Finset.univ : Finset (Fin (m + n))).powersetCard m,
        p (m + n) (polarSlotInput (m + n) s)‖ ≤
        ∑ s ∈ (Finset.univ : Finset (Fin (m + n))).powersetCard m,
          ‖p (m + n) (polarSlotInput (m + n) s)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _s ∈ (Finset.univ : Finset (Fin (m + n))).powersetCard m,
          ‖p (m + n)‖ := by
      apply Finset.sum_le_sum
      intro s _hs
      calc
        ‖p (m + n) (polarSlotInput (m + n) s)‖ ≤
            ‖p (m + n)‖ * ∏ i, ‖polarSlotInput (m + n) s i‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
        _ = ‖p (m + n)‖ := by simp [norm_polarSlotInput]
    _ = ((m + n).choose m : ℝ) * ‖p (m + n)‖ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp

/-- A homogeneous geometric operator-norm bound becomes the natural
binomial bound for its ordinary bivariate polar coefficients. -/
lemma norm_polarCoefficient_le_transportEnvelope
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {p : FormalMultilinearSeries ℝ Domain G} {A s : ℝ}
    (hp : ∀ k, ‖p k‖ ≤ A * s ^ k) (m n : ℕ) :
    ‖polarCoefficient p m n‖ ≤ transportEnvelope A s s m n := by
  calc
    ‖polarCoefficient p m n‖ ≤
        ((m + n).choose m : ℝ) * ‖p (m + n)‖ :=
      norm_polarCoefficient_le p m n
    _ ≤ ((m + n).choose m : ℝ) * (A * s ^ (m + n)) := by
      gcongr
      exact hp (m + n)
    _ = A * ((m + n).choose m : ℝ) * s ^ m * s ^ n := by
      rw [pow_add]
      ring
    _ = transportEnvelope A s s m n := by rfl

/-! ## Formal matrix action bounds on an arbitrary input space -/

section GenericActionDomain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The unsymmetrized matrix action on two blocks of multilinear inputs,
with an arbitrary real normed input space. -/
noncomputable def splitActionOn {i j : ℕ}
    (A : E [×i]→L[ℝ] FirstOrderOperator)
    (u : E [×j]→L[ℝ] FirstOrderState) :
    ContinuousMultilinearMap ℝ (fun _ : Fin i ⊕ Fin j => E)
      FirstOrderState :=
  (((ContinuousLinearMap.compContinuousMultilinearMapL ℝ
      (fun _ : Fin j => E) FirstOrderState FirstOrderState).flip u)
    |>.compContinuousMultilinearMap
      (operatorActionCLM.compContinuousMultilinearMap A)).uncurrySum

/-- `splitActionOn`, with its two finite input blocks identified with a
single block of size `i + j`. -/
noncomputable def splitActionFinOn {i j : ℕ}
    (A : E [×i]→L[ℝ] FirstOrderOperator)
    (u : E [×j]→L[ℝ] FirstOrderState) :
    E [×(i + j)]→L[ℝ] FirstOrderState :=
  (splitActionOn A u).domDomCongr finSumFinEquiv

@[simp] lemma splitActionFinOn_apply {i j : ℕ}
    (A : E [×i]→L[ℝ] FirstOrderOperator)
    (u : E [×j]→L[ℝ] FirstOrderState)
    (v : Fin (i + j) → E) :
    splitActionFinOn A u v =
      operatorActionCLM
        (A (v ∘ (finSumFinEquiv ∘ Sum.inl)))
        (u (v ∘ (finSumFinEquiv ∘ Sum.inr))) := by
  rfl

/-- The degree-`i` summand in the formal action at total degree `k`, for an
arbitrary input space. -/
noncomputable def actionHomogeneousOn
    (A : FormalMultilinearSeries ℝ E FirstOrderOperator)
    (u : FormalMultilinearSeries ℝ E FirstOrderState)
    (k i : ℕ) : E [×k]→L[ℝ] FirstOrderState :=
  if hi : i ≤ k then
    (splitActionFinOn (A i) (u (k - i))).domDomCongr
      (finCongr (Nat.add_sub_of_le hi))
  else 0

/-- Formal matrix action on series over an arbitrary real normed input
space.  For `E = Domain`, this is definitionally the original
`formalAction`. -/
noncomputable def formalActionOn
    (A : FormalMultilinearSeries ℝ E FirstOrderOperator)
    (u : FormalMultilinearSeries ℝ E FirstOrderState) :
    FormalMultilinearSeries ℝ E FirstOrderState :=
  fun k => ∑ i ∈ Finset.range (k + 1), actionHomogeneousOn A u k i

/-- The two-coordinate matrix contraction contributes the explicit factor
`2`; no constant depends on the input space. -/
lemma norm_splitActionFinOn_le {i j : ℕ}
    (A : E [×i]→L[ℝ] FirstOrderOperator)
    (u : E [×j]→L[ℝ] FirstOrderState) :
    ‖splitActionFinOn A u‖ ≤ 2 * ‖A‖ * ‖u‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  rw [splitActionFinOn_apply]
  calc
    ‖operatorActionCLM
        (A (v ∘ (finSumFinEquiv ∘ Sum.inl)))
        (u (v ∘ (finSumFinEquiv ∘ Sum.inr)))‖ ≤
      2 * ‖A (v ∘ (finSumFinEquiv ∘ Sum.inl))‖ *
        ‖u (v ∘ (finSumFinEquiv ∘ Sum.inr))‖ :=
      norm_firstOrderOperator_mulVec_le _ _
    _ ≤ 2 * (‖A‖ * ∏ a, ‖v (Fin.castAdd j a)‖) *
        (‖u‖ * ∏ b, ‖v (Fin.natAdd i b)‖) := by
      gcongr
      · simpa only [Function.comp_apply, finSumFinEquiv_apply_left] using
          A.le_opNorm (v ∘ (finSumFinEquiv ∘ Sum.inl))
      · simpa only [Function.comp_apply, finSumFinEquiv_apply_right] using
          u.le_opNorm (v ∘ (finSumFinEquiv ∘ Sum.inr))
    _ = (2 * ‖A‖ * ‖u‖) * ∏ q, ‖v q‖ := by
      rw [Fin.prod_univ_add]
      ring

lemma norm_actionHomogeneousOn_le
    (A : FormalMultilinearSeries ℝ E FirstOrderOperator)
    (u : FormalMultilinearSeries ℝ E FirstOrderState)
    (k i : ℕ) :
    ‖actionHomogeneousOn A u k i‖ ≤
      2 * ‖A i‖ * ‖u (k - i)‖ := by
  unfold actionHomogeneousOn
  split
  next hi =>
    rw [ContinuousMultilinearMap.norm_domDomCongr]
    exact norm_splitActionFinOn_le _ _
  next hi =>
    simp only [norm_zero]
    positivity

/-- Homogeneous norm bound for formal matrix action, valid over every real
normed input space. -/
theorem norm_formalActionOn_le
    (A : FormalMultilinearSeries ℝ E FirstOrderOperator)
    (u : FormalMultilinearSeries ℝ E FirstOrderState)
    (k : ℕ) :
    ‖formalActionOn A u k‖ ≤
      ∑ i ∈ Finset.range (k + 1),
        2 * ‖A i‖ * ‖u (k - i)‖ := by
  unfold formalActionOn
  calc
    ‖∑ i ∈ Finset.range (k + 1), actionHomogeneousOn A u k i‖ ≤
        ∑ i ∈ Finset.range (k + 1),
          ‖actionHomogeneousOn A u k i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1),
        2 * ‖A i‖ * ‖u (k - i)‖ := by
      exact Finset.sum_le_sum fun i hi =>
        norm_actionHomogeneousOn_le A u k i

end GenericActionDomain

/-- Specialization of `norm_formalActionOn_le` to the two-variable domain
used by the reduced stress system. -/
theorem norm_formalAction_le
    (A : OperatorSeries) (u : StateSeries) (k : ℕ) :
    ‖formalAction A u k‖ ≤
      ∑ i ∈ Finset.range (k + 1),
        2 * ‖A i‖ * ‖u (k - i)‖ := by
  change
    ‖formalActionOn A u k‖ ≤
      ∑ i ∈ Finset.range (k + 1),
        2 * ‖A i‖ * ‖u (k - i)‖
  exact norm_formalActionOn_le A u k

/-! ## The Euler derivative at homogeneous degree -/

private lemma norm_changeOriginSeries_one_le
    (p : StateSeries) (k : ℕ) :
    ‖p.changeOriginSeries 1 k‖ ≤ (k + 1 : ℝ) * ‖p (k + 1)‖ := by
  have h := p.nnnorm_changeOriginSeries_le_tsum 1 k
  rw [show 1 + k = k + 1 by omega] at h
  have hcard :
      Fintype.card {s : Finset (Fin (k + 1)) // s.card = k} = k + 1 := by
    simp only [Fintype.card_finset_len, Fintype.card_fin]
    exact Nat.choose_succ_self_right k
  rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, hcard] at h
  exact_mod_cast h

private lemma norm_apply_yDirection_le :
    ‖ContinuousLinearMap.apply ℝ FirstOrderState yDirection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  rw [ContinuousLinearMap.apply_apply]
  calc
    ‖f yDirection‖ ≤ ‖f‖ * ‖yDirection‖ := f.le_opNorm _
    _ = 1 * ‖f‖ := by simp [yDirection, Prod.norm_def]

private lemma norm_derivSeries_le
    (p : StateSeries) (k : ℕ) :
    ‖p.derivSeries k‖ ≤ (k + 1 : ℝ) * ‖p (k + 1)‖ := by
  have hcurry :
      ‖(continuousMultilinearCurryFin1 ℝ Domain FirstOrderState :
        ((Domain [×1]→L[ℝ] FirstOrderState) →L[ℝ]
          Domain →L[ℝ] FirstOrderState))‖ ≤ 1 := by
    change
      ‖(continuousMultilinearCurryFin1 ℝ Domain
        FirstOrderState).toLinearIsometry.toContinuousLinearMap‖ ≤ 1
    exact LinearIsometry.norm_toContinuousLinearMap_le _
  unfold FormalMultilinearSeries.derivSeries
  rw [ContinuousLinearMap.compFormalMultilinearSeries_apply]
  calc
    ‖((continuousMultilinearCurryFin1 ℝ Domain FirstOrderState :
          (Domain [×1]→L[ℝ] FirstOrderState) →L[ℝ]
            Domain →L[ℝ] FirstOrderState)).compContinuousMultilinearMap
        (p.changeOriginSeries 1 k)‖ ≤
        ‖(continuousMultilinearCurryFin1 ℝ Domain FirstOrderState :
          ((Domain [×1]→L[ℝ] FirstOrderState) →L[ℝ]
            Domain →L[ℝ] FirstOrderState))‖ *
          ‖p.changeOriginSeries 1 k‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 1 * ((k + 1 : ℝ) * ‖p (k + 1)‖) := by
      gcongr
      exact norm_changeOriginSeries_one_le p k
    _ = (k + 1 : ℝ) * ‖p (k + 1)‖ := one_mul _

private lemma norm_rawFormalYDerivative_homogeneousOnly_le
    (u : StateSeries) (k : ℕ) :
    ‖rawFormalYDerivative (homogeneousOnly (k + 1) (u (k + 1))) k‖ ≤
      (k + 1 : ℝ) * ‖u (k + 1)‖ := by
  unfold rawFormalYDerivative
  rw [ContinuousLinearMap.compFormalMultilinearSeries_apply]
  calc
    ‖(ContinuousLinearMap.apply ℝ FirstOrderState yDirection)
        |>.compContinuousMultilinearMap
          ((homogeneousOnly (k + 1) (u (k + 1))).derivSeries k)‖ ≤
        ‖ContinuousLinearMap.apply ℝ FirstOrderState yDirection‖ *
          ‖(homogeneousOnly (k + 1) (u (k + 1))).derivSeries k‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 1 * ((k + 1 : ℝ) * ‖u (k + 1)‖) := by
      gcongr
      · exact norm_apply_yDirection_le
      · calc
          ‖(homogeneousOnly (k + 1) (u (k + 1))).derivSeries k‖ ≤
              (k + 1 : ℝ) *
                ‖homogeneousOnly (k + 1) (u (k + 1)) (k + 1)‖ :=
            norm_derivSeries_le _ k
          _ = (k + 1 : ℝ) * ‖u (k + 1)‖ := by
            simp [homogeneousOnly]
    _ = (k + 1 : ℝ) * ‖u (k + 1)‖ := one_mul _

/-- At homogeneous degree `k`, the Euler operator `y ∂y` costs at most the
total-degree factor `k` in operator norm.  The sharper ordinary coefficient
factor is the tangential degree `n`; this coarse bound is used only for the
positive-degree nonlinear remainder. -/
lemma norm_formalEulerY_le (u : StateSeries) (k : ℕ) :
    ‖formalEulerY u k‖ ≤ (k : ℝ) * ‖u k‖ := by
  cases k with
  | zero =>
      simp [formalEulerY, multiplyByY]
  | succ k =>
      unfold formalEulerY
      rw [multiplyByY_succ, ContinuousLinearMap.uncurryLeft_norm,
        ContinuousLinearMap.norm_smulRight_apply]
      calc
        ‖yProjection‖ *
            ‖rawFormalYDerivative
              (homogeneousOnly (k + 1) (u (k + 1))) k‖ ≤
            1 * ((k + 1 : ℝ) * ‖u (k + 1)‖) := by
          gcongr
          · exact ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
          · exact norm_rawFormalYDerivative_homogeneousOnly_le u k
        _ = ((k + 1 : ℕ) : ℝ) * ‖u (k + 1)‖ := by simp

/-! ## Exact ordinary coefficients of the constant Euler transport -/

private lemma homogeneousOnly_sum
    (q : Domain [×k]→L[ℝ] FirstOrderState) (z : Domain) :
    (homogeneousOnly k q).sum z = q (fun _ : Fin k => z) := by
  unfold FormalMultilinearSeries.sum
  rw [tsum_eq_single k]
  · simp [homogeneousOnly]
  · intro l hl
    simp [homogeneousOnly, Ne.symm hl]

private lemma homogeneousOnly_finite
    (q : Domain [×k]→L[ℝ] FirstOrderState) :
    ∀ d, k + 1 ≤ d → homogeneousOnly k q d = 0 := by
  intro d hd
  simp only [homogeneousOnly]
  split
  next h => omega
  next => rfl

/-- A direct bridge from the coefficient-local formal derivative to the
derivative of the corresponding finite homogeneous polynomial. -/
private lemma rawFormalYDerivative_homogeneousOnly_apply_diag
    (q : Domain [×(k + 1)]→L[ℝ] FirstOrderState)
    (z : Domain) :
    rawFormalYDerivative (homogeneousOnly (k + 1) q) k
        (fun _ : Fin k => z) =
      (continuousMultilinearCurryFin1 ℝ Domain FirstOrderState
        ((homogeneousOnly (k + 1) q).changeOrigin z 1)) yDirection := by
  unfold rawFormalYDerivative
  simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply',
    ContinuousLinearMap.apply_apply, FormalMultilinearSeries.derivSeries,
    ContinuousLinearMap.compFormalMultilinearSeries_apply',
    continuousMultilinearCurryFin1_apply]
  unfold FormalMultilinearSeries.changeOrigin FormalMultilinearSeries.sum
  rw [ContinuousMultilinearMap.tsum_eval]
  · rw [tsum_eq_single k]
    · rfl
    · intro l hl
      have hdeg : k + 1 ≠ 1 + l := by omega
      unfold FormalMultilinearSeries.changeOriginSeries
      simp [FormalMultilinearSeries.changeOriginSeriesTerm,
        homogeneousOnly, hdeg]
  · apply summable_of_ne_finset_zero (s := {k})
    intro l hl
    have hlk : l ≠ k := by simpa using hl
    have hdeg : k + 1 ≠ 1 + l := by omega
    unfold FormalMultilinearSeries.changeOriginSeries
    rw [sum_apply]
    apply Finset.sum_eq_zero
    intro s hs
    have hpzero : homogeneousOnly (k + 1) q (1 + l) = 0 := by
      simp [homogeneousOnly, hdeg]
    have hterm :
        (homogeneousOnly (k + 1) q).changeOriginSeriesTerm
          1 l s s.2 = 0 := by
      unfold FormalMultilinearSeries.changeOriginSeriesTerm
      rw [hpzero]
      dsimp only
      exact LinearEquiv.map_zero _
    rw [hterm]
    rfl

private lemma hasDerivAt_stateBivariateFMS_homogeneous_y
    (a : BivariateStateCoeff) (k : ℕ) (x y : ℝ) :
    HasDerivAt
      (fun t => stateBivariateFMS a k (fun _ : Fin k => (x, t)))
      (∑ m ∈ Finset.range (k + 1),
        (x ^ m * ((k - m : ℕ) : ℝ) * y ^ (k - m - 1)) •
          a m (k - m)) y := by
  have hsum : HasDerivAt
      (fun t => ∑ m ∈ Finset.range (k + 1),
        (x ^ m * t ^ (k - m)) • a m (k - m))
      (∑ m ∈ Finset.range (k + 1),
        (x ^ m * ((k - m : ℕ) : ℝ) * y ^ (k - m - 1)) •
          a m (k - m)) y := by
    apply HasDerivAt.fun_sum
    intro m hm
    convert ((hasDerivAt_pow (k - m) y).const_mul (x ^ m)).smul_const
      (a m (k - m)) using 1
    all_goals ring_nf
  apply hsum.congr_of_eventuallyEq
  filter_upwards [] with t
  exact stateBivariateFMS_apply_diag a k x t

private lemma rawFormalYDerivative_stateBivariateFMS_apply_diag
    (a : BivariateStateCoeff) (k : ℕ) (x y : ℝ) :
    rawFormalYDerivative
        (homogeneousOnly (k + 1) (stateBivariateFMS a (k + 1))) k
        (fun _ : Fin k => (x, y)) =
      ∑ m ∈ Finset.range (k + 2),
        (x ^ m * (((k + 1 - m : ℕ) : ℝ)) *
          y ^ (k + 1 - m - 1)) • a m (k + 1 - m) := by
  let p : StateSeries :=
    homogeneousOnly (k + 1) (stateBivariateFMS a (k + 1))
  have hpfinite : ∀ d, k + 2 ≤ d → p d = 0 := by
    exact homogeneousOnly_finite (stateBivariateFMS a (k + 1))
  have hp := p.hasFiniteFPowerSeriesOnBall_of_finite hpfinite
  have hF := hp.toHasFPowerSeriesOnBall.hasFDerivAt
    (y := ((x, y) : Domain)) (by simp)
  have hF' : HasFDerivAt p.sum
      (continuousMultilinearCurryFin1 ℝ Domain FirstOrderState
        (p.changeOrigin (x, y) 1)) (x, y) := by
    simpa using hF
  have hslice := hF'.comp_hasDerivAt y
    (hasFDerivAt_prodMk_right x y).hasDerivAt
  have hpoly := hasDerivAt_stateBivariateFMS_homogeneous_y
    a (k + 1) x y
  have hpSum : (fun t => p.sum (x, t)) =
      (fun t => stateBivariateFMS a (k + 1)
        (fun _ : Fin (k + 1) => (x, t))) := by
    funext t
    exact homogeneousOnly_sum _ _
  have hslice' : HasDerivAt
      (fun t => stateBivariateFMS a (k + 1)
        (fun _ : Fin (k + 1) => (x, t)))
      ((continuousMultilinearCurryFin1 ℝ Domain FirstOrderState
        (p.changeOrigin (x, y) 1)) yDirection) y := by
    simpa only [Function.comp_def, ContinuousLinearMap.inr_apply,
      one_smul, yDirection, hpSum] using hslice
  have heq := hslice'.unique hpoly
  rw [rawFormalYDerivative_homogeneousOnly_apply_diag]
  exact heq

/-- Ordinary bivariate coefficients after applying `y ∂y`. -/
def eulerCoefficientArray (a : BivariateStateCoeff) : BivariateStateCoeff :=
  fun m n => (n : ℝ) • a m n

/-- Diagonal evaluation of the coefficient-local formal Euler operator is
the ordinary polynomial whose `(m,n)` coefficient is `n a[m,n]`. -/
lemma formalEulerY_stateBivariateFMS_apply_diag
    (a : BivariateStateCoeff) (k : ℕ) (x y : ℝ) :
    formalEulerY (stateBivariateFMS a) k (fun _ : Fin k => (x, y)) =
      stateBivariateFMS (eulerCoefficientArray a) k
        (fun _ : Fin k => (x, y)) := by
  cases k with
  | zero =>
      simp [formalEulerY, multiplyByY, stateBivariateFMS_apply_diag,
        eulerCoefficientArray]
  | succ k =>
      change
        multiplyByY
            (rawFormalYDerivative
              (homogeneousOnly (k + 1) (stateBivariateFMS a (k + 1))))
            (k + 1) (fun _ : Fin (k + 1) => (x, y)) = _
      rw [multiplyByY_apply_diag,
        rawFormalYDerivative_stateBivariateFMS_apply_diag,
        stateBivariateFMS_apply_diag, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hmk : m ≤ k + 1 :=
        Nat.le_of_lt_succ (Finset.mem_range.mp hm)
      let n := k + 1 - m
      change
        y • ((x ^ m * (n : ℝ) * y ^ (n - 1)) • a m n) =
          (x ^ m * y ^ n) • ((n : ℝ) • a m n)
      by_cases hn : n = 0
      · simp [hn]
      · obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hn
        rw [hr]
        simp only [Nat.succ_sub_one, pow_succ, smul_smul]
        congr 1
        ring

private lemma polarCoefficient_eq_of_apply_diag_eq
    (p q : StateSeries) (k : ℕ)
    (hdiag : ∀ z : Domain,
      p k (fun _ : Fin k => z) = q k (fun _ : Fin k => z))
    {m : ℕ} (hm : m ≤ k) :
    polarCoefficient p m (k - m) =
      polarCoefficient q m (k - m) := by
  funext i
  rw [CKPolarUniqueness.formal_polarCoefficient_eq_evaluation_polarCoefficient,
    CKPolarUniqueness.formal_polarCoefficient_eq_evaluation_polarCoefficient,
    ← CKPolarUniqueness.polarCoefficient_componentSeries,
    ← CKPolarUniqueness.polarCoefficient_componentSeries,
    ← CKPolarUniqueness.coeff_scalarDiagonalPolynomial _ hm,
    ← CKPolarUniqueness.coeff_scalarDiagonalPolynomial _ hm]
  congr 1
  apply Polynomial.funext
  intro x
  rw [CKPolarUniqueness.eval_scalarDiagonalPolynomial,
    CKPolarUniqueness.eval_scalarDiagonalPolynomial]
  exact congrFun (hdiag (x, 1)) i

/-- Polar extraction is a left inverse to the canonical construction of a
bivariate formal multilinear series. -/
lemma polarCoefficient_stateBivariateFMS
    (a : BivariateStateCoeff) (m n : ℕ) :
    polarCoefficient (stateBivariateFMS a) m n = a m n := by
  let k := m + n
  have hm : m ≤ k := Nat.le_add_right m n
  funext i
  rw [← show k - m = n by simp [k]]
  rw [CKPolarUniqueness.formal_polarCoefficient_eq_evaluation_polarCoefficient,
    ← CKPolarUniqueness.polarCoefficient_componentSeries,
    ← CKPolarUniqueness.coeff_scalarDiagonalPolynomial _ hm]
  have hpoly :
      CKPolarUniqueness.scalarDiagonalPolynomial
          (CKPolarUniqueness.componentSeries (stateBivariateFMS a) i) k =
        ∑ r ∈ Finset.range (k + 1),
          Polynomial.monomial r (a r (k - r) i) := by
    apply Polynomial.funext
    intro x
    rw [CKPolarUniqueness.eval_scalarDiagonalPolynomial,
      Polynomial.eval_finsetSum,
      CKPolarUniqueness.componentSeries_apply,
      stateBivariateFMS_apply_diag]
    simp only [Finset.sum_apply, Pi.smul_apply, Polynomial.eval_monomial,
      one_pow, mul_one, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [hpoly, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single m]
  · simp [k]
  · intro r hr hrm
    simp [Polynomial.coeff_monomial, hrm]
  · intro hmem
    exact (hmem (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))).elim

/-- Exact ordinary coefficient formula for the Euler operator. -/
theorem polarCoefficient_formalEulerY_stateBivariateFMS
    (a : BivariateStateCoeff) (m n : ℕ) :
    polarCoefficient (formalEulerY (stateBivariateFMS a)) m n =
      (n : ℝ) • a m n := by
  let k := m + n
  have hm : m ≤ k := Nat.le_add_right m n
  have hkn : k - m = n := by simp [k]
  calc
    polarCoefficient (formalEulerY (stateBivariateFMS a)) m n =
        polarCoefficient (stateBivariateFMS (eulerCoefficientArray a)) m n := by
      rw [← hkn]
      apply polarCoefficient_eq_of_apply_diag_eq _ _ k
        (fun z => formalEulerY_stateBivariateFMS_apply_diag
          a k z.1 z.2) hm
    _ = eulerCoefficientArray a m n := polarCoefficient_stateBivariateFMS _ _ _
    _ = (n : ℝ) • a m n := rfl

/-- A constant operator-valued formal series acts coefficientwise on
diagonal homogeneous evaluations. -/
lemma formalAction_const_apply_diag
    (A0 : FirstOrderOperator) (u : StateSeries) (k : ℕ) (z : Domain) :
    formalAction (constFormalMultilinearSeries ℝ Domain A0)
        u k (fun _ : Fin k => z) =
      Matrix.mulVec A0 (u k (fun _ : Fin k => z)) := by
  rw [CKFormalActionEvaluation.formalAction_apply_diag]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    rw [constFormalMultilinearSeries_apply_of_nonzero hi0]
    simp
  · simp

/-- Ordinary coefficients of a constant matrix applied after `y ∂y`. -/
def constantEulerActionCoefficientArray
    (A0 : FirstOrderOperator) (a : BivariateStateCoeff) :
    BivariateStateCoeff :=
  fun m n => (n : ℝ) • Matrix.mulVec A0 (a m n)

lemma formalAction_const_formalEulerY_stateBivariateFMS_apply_diag
    (A0 : FirstOrderOperator) (a : BivariateStateCoeff)
    (k : ℕ) (x y : ℝ) :
    formalAction (constFormalMultilinearSeries ℝ Domain A0)
        (formalEulerY (stateBivariateFMS a)) k
        (fun _ : Fin k => (x, y)) =
      stateBivariateFMS (constantEulerActionCoefficientArray A0 a) k
        (fun _ : Fin k => (x, y)) := by
  rw [formalAction_const_apply_diag,
    formalEulerY_stateBivariateFMS_apply_diag,
    stateBivariateFMS_apply_diag, stateBivariateFMS_apply_diag]
  change
    operatorActionCLM A0
        (∑ m ∈ Finset.range (k + 1),
          (x ^ m * y ^ (k - m)) • eulerCoefficientArray a m (k - m)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [map_smul]
  simp [eulerCoefficientArray, constantEulerActionCoefficientArray]

/-- Exact constant-principal transport formula: polar extraction of
`A₀ (y ∂y U)` is `n A₀ a[m,n]`, with no total-degree loss. -/
theorem polarCoefficient_formalAction_const_formalEulerY_stateBivariateFMS
    (A0 : FirstOrderOperator) (a : BivariateStateCoeff) (m n : ℕ) :
    polarCoefficient
        (formalAction (constFormalMultilinearSeries ℝ Domain A0)
          (formalEulerY (stateBivariateFMS a))) m n =
      (n : ℝ) • Matrix.mulVec A0 (a m n) := by
  let k := m + n
  have hm : m ≤ k := Nat.le_add_right m n
  have hkn : k - m = n := by simp [k]
  calc
    polarCoefficient
        (formalAction (constFormalMultilinearSeries ℝ Domain A0)
          (formalEulerY (stateBivariateFMS a))) m n =
        polarCoefficient
          (stateBivariateFMS (constantEulerActionCoefficientArray A0 a))
          m n := by
      rw [← hkn]
      apply polarCoefficient_eq_of_apply_diag_eq _ _ k
        (fun z =>
          formalAction_const_formalEulerY_stateBivariateFMS_apply_diag
            A0 a k z.1 z.2) hm
    _ = constantEulerActionCoefficientArray A0 a m n :=
      polarCoefficient_stateBivariateFMS _ _ _
    _ = (n : ℝ) • Matrix.mulVec A0 (a m n) := rfl

/-! ## Equation-specific analytic composition bounds -/

/-- The explicit geometric rate produced when the principal Taylor germ is
composed with a geometrically bounded formal phase. -/
noncomputable def principalCompositionRate (P : Params) (D s : ℝ) : ℝ :=
  2 * max 1 (((firstOrderPrincipalOriginMajorant P).radius : ℝ)⁻¹ * D) * s

/-- The analogous rate for the derivative-free source Taylor germ. -/
noncomputable def sourceCompositionRate (P : Params) (D s : ℝ) : ℝ :=
  2 * max 1 (((firstOrderSourceOriginMajorant P).radius : ℝ)⁻¹ * D) * s

theorem norm_principal_comp_phase_le_geometric
    (P : Params) (u : StateSeries) {D s : ℝ}
    (hD : 0 ≤ D) (hs : 0 ≤ s)
    (hphase : ∀ k, ‖phaseSeries u k‖ ≤ D * s ^ k) :
    ∀ k,
      ‖(firstOrderPrincipalOriginMajorant P).series.comp (phaseSeries u) k‖ ≤
        (firstOrderPrincipalOriginMajorant P).coefficientBound *
          principalCompositionRate P D s ^ k := by
  simpa only [principalCompositionRate] using
    (CKFMSCompositionMajorant.LocalAnalyticMajorant.norm_comp_le_geometric
      (firstOrderPrincipalOriginMajorant P) (phaseSeries u) hD hs hphase)

theorem norm_source_comp_phase_le_geometric
    (P : Params) (u : StateSeries) {D s : ℝ}
    (hD : 0 ≤ D) (hs : 0 ≤ s)
    (hphase : ∀ k, ‖phaseSeries u k‖ ≤ D * s ^ k) :
    ∀ k,
      ‖(firstOrderSourceOriginMajorant P).series.comp (phaseSeries u) k‖ ≤
        (firstOrderSourceOriginMajorant P).coefficientBound *
          sourceCompositionRate P D s ^ k := by
  simpa only [sourceCompositionRate] using
    (CKFMSCompositionMajorant.LocalAnalyticMajorant.norm_comp_le_geometric
      (firstOrderSourceOriginMajorant P) (phaseSeries u) hD hs hphase)

/-- The homogeneous source-composition estimate transfers to ordinary
bivariate polar coefficients with the binomial transport weight. -/
theorem norm_source_polarCoefficient_le_transportEnvelope
    (P : Params) (u : StateSeries) {D s : ℝ}
    (hD : 0 ≤ D) (hs : 0 ≤ s)
    (hphase : ∀ k, ‖phaseSeries u k‖ ≤ D * s ^ k)
    (m n : ℕ) :
    ‖polarCoefficient
        ((firstOrderSourceOriginMajorant P).series.comp (phaseSeries u)) m n‖ ≤
      transportEnvelope
        (firstOrderSourceOriginMajorant P).coefficientBound
        (sourceCompositionRate P D s) (sourceCompositionRate P D s) m n := by
  apply norm_polarCoefficient_le_transportEnvelope
  exact norm_source_comp_phase_le_geometric P u hD hs hphase

/-! ## Stress-system Fuchsian transport and residual -/

/-- The constant principal operator transports the current coefficient
through the Euler factor `n`. -/
noncomputable def firstOrderBaseTransport
    (P : Params) (a : BivariateStateCoeff) : BivariateStateCoeff :=
  fun m n => Matrix.mulVec
    (firstOrderPrincipalArray P firstOrderOrigin) (a m n)

/-- Everything in the formal right-hand side except the constant-principal
Euler transport.  Bounding this residual is the sole equation-specific
nonlinear estimate required by the convergence theorem below. -/
noncomputable def firstOrderNonlinearResidual
    (P : Params) (a : BivariateStateCoeff) : BivariateStateCoeff :=
  fun m n =>
    reducedArrayRHS
        (firstOrderPrincipalOriginMajorant P).series
        (firstOrderSourceOriginMajorant P).series a m n -
      (n : ℝ) • firstOrderBaseTransport P a m n

/-- The chosen Taylor germ has the actual principal matrix as its constant
coefficient. -/
theorem firstOrderPrincipalOriginMajorant_zero
    (P : Params) (z : Fin 0 → FirstOrderPhase) :
    (firstOrderPrincipalOriginMajorant P).series 0 z =
      firstOrderPrincipalArray P firstOrderOrigin :=
  (firstOrderPrincipalOriginMajorant P).hasFPowerSeriesOnBall.coeff_zero z

/-- The residual coefficient is causal in total degree. -/
theorem firstOrderNonlinearResidual_causal
    (P : Params) {a c : BivariateStateCoeff} {m n : ℕ}
    (h : CoeffAgreeUpToTotal (m + n) a c) :
    firstOrderNonlinearResidual P a m n =
      firstOrderNonlinearResidual P c m n := by
  unfold firstOrderNonlinearResidual firstOrderBaseTransport
  rw [reducedArrayRHS_causal _ _ h, h m n le_rfl]

theorem norm_firstOrderBaseTransport_le
    (P : Params) (a : BivariateStateCoeff) (m n : ℕ) :
    ‖firstOrderBaseTransport P a m n‖ ≤
      (2 * ‖firstOrderPrincipalArray P firstOrderOrigin‖) * ‖a m n‖ := by
  exact CKBivariateConvolutionMajorant.norm_firstOrderOperator_mulVec_le
    (firstOrderPrincipalArray P firstOrderOrigin) (a m n)

/-- The formal recurrence, rewritten in the exact transport-plus-residual
shape consumed by the Fuchsian majorant theorem. -/
theorem firstOrderFormalCoefficients_scaled_recurrence
    (P : Params) (m n : ℕ) :
    ((m + 1 : ℕ) : ℝ) • firstOrderFormalCoefficients P (m + 1) n =
      (n : ℝ) • firstOrderBaseTransport P
          (firstOrderFormalCoefficients P) m n +
        firstOrderNonlinearResidual P
          (firstOrderFormalCoefficients P) m n := by
  have hrec := firstOrderFormalCoefficients_satisfiesRecurrence P m n
  rw [hrec]
  unfold reducedNextXCoefficient firstOrderNonlinearResidual
  have hm : (((m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [smul_smul, mul_inv_cancel₀ hm, one_smul]
  abel

/-- A named certificate for the one genuinely nonlinear coefficient
inequality left by the abstract analytic and Fuchsian infrastructure. -/
def HasFirstOrderResidualMajorant
    (P : Params) (a : BivariateStateCoeff)
    (K M Q R S : ℝ) : Prop :=
  ∀ m n,
    ‖firstOrderNonlinearResidual P a m n‖ ≤
      M * diagonalConvolution (catalanEnvelope K Q)
        (catalanEnvelope K Q) R S m n

/-- Once the residual estimate holds, the formal stress-system coefficients
have a common product-geometric bound.  The rates are completely explicit;
the factor `2` in the linear constant is the two-coordinate matrix
contraction cost. -/
theorem firstOrderFormalCoefficients_component_geometricBound
    (P : Params) {K M Q R S : ℝ}
    (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hlinear : 2 * ‖firstOrderPrincipalArray P firstOrderOrigin‖ ≤
      R * K * Q)
    (hquadratic : M ≤ R * Q)
    (hresidual : HasFirstOrderResidualMajorant P
      (firstOrderFormalCoefficients P) K M Q R S) :
    ∀ i,
      GeometricBound
        (fun m n => firstOrderFormalCoefficients P m n i) K
        (8 * (K * Q) * R) (8 * (K * Q) * S) := by
  apply CKBivariateConvolutionMajorant.component_geometricBound_of_reduced_vector_recurrence
    (a := firstOrderFormalCoefficients P)
    (transport := firstOrderBaseTransport P (firstOrderFormalCoefficients P))
    (nonlinear := firstOrderNonlinearResidual P (firstOrderFormalCoefficients P))
    (f := fun _ _ => 0) (K := K)
    (L := 2 * ‖firstOrderPrincipalArray P firstOrderOrigin‖)
    (M := M) (G := 0) (Q := Q) (R := R) (S := S)
  · exact hK
  · positivity
  · exact hQ
  · exact hR
  · exact hS
  · exact hlinear
  · simpa using hquadratic
  · intro n
    rw [firstOrderFormalCoefficients_zero_x]
    simpa only [norm_zero] using
      mul_nonneg (pow_nonneg hS n) (catalanEnvelope_nonneg hK hQ n)
  · intro m n
    simp
  · exact norm_firstOrderBaseTransport_le P
      (firstOrderFormalCoefficients P)
  · intro m n
    simpa [HasFirstOrderResidualMajorant] using hresidual m n
  · exact firstOrderFormalCoefficients_scaled_recurrence P

/-- Vector-valued packaging of the preceding component estimates, ready for
the analytic series-realization layer. -/
theorem firstOrderFormalCoefficients_vectorGeometricBound
    (P : Params) {K M Q R S : ℝ}
    (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hlinear : 2 * ‖firstOrderPrincipalArray P firstOrderOrigin‖ ≤
      R * K * Q)
    (hquadratic : M ≤ R * Q)
    (hresidual : HasFirstOrderResidualMajorant P
      (firstOrderFormalCoefficients P) K M Q R S) :
    CKVectorAnalyticEvaluation.VectorGeometricBound
      (CKVectorAnalyticEvaluation.stateComponents
        (firstOrderFormalCoefficients P)) K
      (8 * (K * Q) * R) (8 * (K * Q) * S) := by
  refine ⟨?_⟩
  exact firstOrderFormalCoefficients_component_geometricBound P
    hK hQ hR hS hlinear hquadratic hresidual

end
end CKFirstOrderConvergence
end StressTensor
