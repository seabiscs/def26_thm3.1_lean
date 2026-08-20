import StressTensor.CKFormalActionEvaluation
import StressTensor.CKFormalRecurrenceDiagonalIdentity
import StressTensor.CKPolarUniqueness
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Analytic competitors satisfy the reduced coefficient recurrence

This file is the coefficient-extraction half of the analytic uniqueness
argument.  Its main technical point is that the deliberately nonsymmetric
Cauchy representative `formalAction` has the same diagonal homogeneous
terms as every analytic power-series representative of the corresponding
pointwise matrix-vector action.  We prove this without imposing an
operator-norm convergence hypothesis on that particular representative:
restriction to each one-dimensional line turns the assertion into ordinary
uniqueness of convergent power series.
-/

namespace StressTensor
namespace CKAnalyticCompetitorRecurrence

open CKFirstOrderFormalSystem CKFormalActionEvaluation
  CKFirstOrderConvergence CKFormalDiagonalCongruence
  CKFormalRecurrenceDiagonalIdentity CKPolarUniqueness

noncomputable section

/-! ## One-dimensional restrictions of the custom Cauchy representative -/

/-- The continuous linear parametrization of the line through `z`. -/
def scalarLine (z : Domain) : ℝ →L[ℝ] Domain :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight z

@[simp] theorem scalarLine_apply (z : Domain) (t : ℝ) :
    scalarLine z t = t • z := rfl

/-- Along every line through the origin, the custom Cauchy representative
`formalAction A u` is a genuine power series for pointwise matrix-vector
action.  This linewise statement is all that polarization needs. -/
theorem hasFPowerSeriesAt_formalAction_comp_scalarLine
    {Afun : Domain → FirstOrderOperator}
    {ufun : Domain → FirstOrderState}
    {A : OperatorSeries} {u : StateSeries}
    (hA : HasFPowerSeriesAt Afun A 0)
    (hu : HasFPowerSeriesAt ufun u 0)
    (z : Domain) :
    HasFPowerSeriesAt
      (fun t : ℝ => Matrix.mulVec (Afun (t • z)) (ufun (t • z)))
      ((formalAction A u).compContinuousLinearMap (scalarLine z)) 0 := by
  have hAline : HasFPowerSeriesAt (Afun ∘ scalarLine z)
      (A.compContinuousLinearMap (scalarLine z)) 0 :=
    by
      have hA' : HasFPowerSeriesAt Afun A (scalarLine z 0) := by
        simpa only [scalarLine_apply, zero_smul] using hA
      exact hA'.compContinuousLinearMap
  have huline : HasFPowerSeriesAt (ufun ∘ scalarLine z)
      (u.compContinuousLinearMap (scalarLine z)) 0 :=
    by
      have hu' : HasFPowerSeriesAt ufun u (scalarLine z 0) := by
        simpa only [scalarLine_apply, zero_smul] using hu
      exact hu'.compContinuousLinearMap
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [hAline.eventually_hasSum, huline.eventually_hasSum,
    Metric.eball_mem_nhds (0 : ℝ) hAline.radius_pos,
    Metric.eball_mem_nhds (0 : ℝ) huline.radius_pos] with t hAt hut htA htu
  have hAnorm : Summable (fun n : ℕ =>
      ‖A n (fun _ : Fin n => t • z)‖) := by
    refine (A.compContinuousLinearMap (scalarLine z)).summable_norm_apply htA |>.congr ?_
    intro n
    rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
    apply congrArg norm
    congr 1
  have hunorm : Summable (fun n : ℕ =>
      ‖u n (fun _ : Fin n => t • z)‖) := by
    refine (u.compContinuousLinearMap (scalarLine z)).summable_norm_apply htu |>.congr ?_
    intro n
    rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
    apply congrArg norm
    congr 1
  have hAt' : HasSum (fun n : ℕ =>
      A n (fun _ : Fin n => t • z)) (Afun (t • z)) := by
    have hx : HasSum (fun n : ℕ => A n (fun _ : Fin n => t • z))
        ((Afun ∘ scalarLine z) (0 + t)) := hAt.congr_fun (fun n => by
      rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
      congr 1)
    simpa only [Function.comp_apply, zero_add, scalarLine_apply] using hx
  have hut' : HasSum (fun n : ℕ =>
      u n (fun _ : Fin n => t • z)) (ufun (t • z)) := by
    have hx : HasSum (fun n : ℕ => u n (fun _ : Fin n => t • z))
        ((ufun ∘ scalarLine z) (0 + t)) := hut.congr_fun (fun n => by
      rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
      congr 1)
    simpa only [Function.comp_apply, zero_add, scalarLine_apply] using hx
  have hs := hasSum_formalAction_apply_diag_of_summable_norm
    A u (t • z) hAt' hut' hAnorm hunorm
  have hsline : HasSum (fun n : ℕ =>
      ((formalAction A u).compContinuousLinearMap (scalarLine z)) n
        (fun _ : Fin n => t))
      (Matrix.mulVec (Afun (t • z)) (ufun (t • z))) := by
    refine hs.congr_fun ?_
    intro n
    rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
    congr 1
  simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    zero_add] using hsline

/-- Any analytic FMS for the pointwise matrix-vector action has the same
homogeneous diagonal as the custom Cauchy representative `formalAction`. -/
theorem formalAction_diagonal_eq_of_hasFPowerSeriesAt
    {Afun : Domain → FirstOrderOperator}
    {ufun : Domain → FirstOrderState}
    {wfun : Domain → FirstOrderState}
    {A : OperatorSeries} {u w : StateSeries}
    (hA : HasFPowerSeriesAt Afun A 0)
    (hu : HasFPowerSeriesAt ufun u 0)
    (hw : HasFPowerSeriesAt wfun w 0)
    (hpoint : ∀ z, wfun z = Matrix.mulVec (Afun z) (ufun z))
    (k : ℕ) (z : Domain) :
    w k (fun _ : Fin k => z) =
      formalAction A u k (fun _ : Fin k => z) := by
  have hwline : HasFPowerSeriesAt (wfun ∘ scalarLine z)
      (w.compContinuousLinearMap (scalarLine z)) 0 :=
    by
      have hw' : HasFPowerSeriesAt wfun w (scalarLine z 0) := by
        simpa only [scalarLine_apply, zero_smul] using hw
      exact hw'.compContinuousLinearMap
  have hcustom := hasFPowerSeriesAt_formalAction_comp_scalarLine hA hu z
  have hwline' : HasFPowerSeriesAt
      (fun t : ℝ => Matrix.mulVec (Afun (t • z)) (ufun (t • z)))
      (w.compContinuousLinearMap (scalarLine z)) 0 := by
    apply hwline.congr
    filter_upwards [] with t
    simp only [Function.comp_apply, scalarLine_apply]
    exact hpoint _
  have heq := hwline'.eq_formalMultilinearSeries hcustom
  have hone := congrArg (fun p : FormalMultilinearSeries ℝ ℝ FirstOrderState =>
    p k (fun _ : Fin k => (1 : ℝ))) heq
  rw [FormalMultilinearSeries.compContinuousLinearMap_apply,
    FormalMultilinearSeries.compContinuousLinearMap_apply] at hone
  convert hone using 1 <;> congr 1 <;> funext i <;>
    simp only [Function.comp_apply, scalarLine_apply, one_smul]

/-! ## The phase and directional-derivative germs -/

/-- The sparse `linearSeries` used by the formal system is Mathlib's
canonical power series of a continuous linear map at the origin. -/
theorem linearSeries_eq_fpowerSeries (l : Domain →L[ℝ] ℝ) :
    linearSeries l = l.fpowerSeries 0 := by
  ext n
  rcases n with (_ | _ | n)
  · simp [linearSeries]
  · rfl
  · rfl

theorem hasFPowerSeriesAt_linearSeries (l : Domain →L[ℝ] ℝ) :
    HasFPowerSeriesAt l (linearSeries l) 0 := by
  rw [linearSeries_eq_fpowerSeries]
  exact l.hasFPowerSeriesAt 0

theorem hasFPowerSeriesAt_ySeries :
    HasFPowerSeriesAt (fun z : Domain => z.2) ySeries 0 := by
  have h := hasFPowerSeriesAt_linearSeries yProjection
  change HasFPowerSeriesAt yProjection ySeries 0 at h
  convert h using 1
  funext z
  rfl

/-- Coordinate projection of a state-valued analytic germ has exactly the
formal series `stateComponent`. -/
theorem hasFPowerSeriesAt_stateComponent
    {U : Domain → FirstOrderState} {u : StateSeries}
    (hu : HasFPowerSeriesAt U u 0) (i : Fin 2) :
    HasFPowerSeriesAt (fun z => U z i) (stateComponent i u) 0 := by
  rcases hu with ⟨r, hu⟩
  refine ⟨r, ?_⟩
  have h := (ContinuousLinearMap.proj (R := ℝ) i)
    |>.comp_hasFPowerSeriesOnBall hu
  change HasFPowerSeriesOnBall
    ((ContinuousLinearMap.proj (R := ℝ) i) ∘ U)
    (stateComponent i u) 0 r at h
  convert h using 1
  funext z
  rfl

/-- The formal phase `(y,U₀,U₁)` represents the corresponding actual
phase of every analytic state germ. -/
theorem hasFPowerSeriesAt_phaseSeries
    {U : Domain → FirstOrderState} {u : StateSeries}
    (hu : HasFPowerSeriesAt U u 0) :
    HasFPowerSeriesAt
      (fun z => firstOrderPhase z.2 (U z 0) (U z 1))
      (phaseSeries u) 0 := by
  have hpi : ∀ i : Fin 3, HasFPowerSeriesAt
      (fun z : Domain => Fin.cases z.2 (fun j : Fin 2 => U z j) i)
      (Fin.cases ySeries (fun j : Fin 2 => stateComponent j u) i) 0 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hasFPowerSeriesAt_ySeries
    · exact hasFPowerSeriesAt_stateComponent hu j
  have hp := HasFPowerSeriesAt.pi hpi
  change HasFPowerSeriesAt
    (fun z i => Fin.cases z.2 (fun j : Fin 2 => U z j) i)
    (phaseSeries u) 0 at hp
  convert hp using 1
  funext z i
  fin_cases i <;> rfl

/-- Differentiating an analytic state FMS and evaluating its derivative in
the fixed `y` direction gives `rawFormalYDerivative`. -/
theorem hasFPowerSeriesAt_rawFormalYDerivative
    {U : Domain → FirstOrderState} {u : StateSeries}
    (hu : HasFPowerSeriesAt U u 0) :
    HasFPowerSeriesAt
      (fun z => fderiv ℝ U z yDirection)
      (rawFormalYDerivative u) 0 := by
  rcases hu with ⟨r, hu⟩
  refine ⟨r, ?_⟩
  have hd := hu.fderiv
  have he := (ContinuousLinearMap.apply ℝ FirstOrderState yDirection)
    |>.comp_hasFPowerSeriesOnBall hd
  change HasFPowerSeriesOnBall
    ((ContinuousLinearMap.apply ℝ FirstOrderState yDirection) ∘
      fderiv ℝ U)
    (rawFormalYDerivative u) 0 r at he
  convert he using 1
  funext z
  rfl

/-- The coefficient-local derivative used for causality agrees with the
ordinary derivative series. -/
lemma derivSeries_coeff_congr
    {p q : StateSeries} {k : ℕ} (h : p (k + 1) = q (k + 1)) :
    p.derivSeries k = q.derivSeries k := by
  have hc : p.changeOriginSeries 1 k = q.changeOriginSeries 1 k := by
    unfold FormalMultilinearSeries.changeOriginSeries
    apply Finset.sum_congr rfl
    intro s hs
    unfold FormalMultilinearSeries.changeOriginSeriesTerm
    have h' : p (1 + k) = q (1 + k) := by
      rw [Nat.add_comm 1 k]
      exact h
    let a := ContinuousMultilinearMap.curryFinFinset
      ℝ Domain FirstOrderState s.2
      (by rw [Finset.card_compl, Fintype.card_fin, s.2,
        add_tsub_cancel_right])
    change a (p (1 + k)) = a (q (1 + k))
    exact congrArg a h'
  unfold FormalMultilinearSeries.derivSeries
  simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply]
  rw [hc]

theorem formalYDerivative_eq_rawFormalYDerivative (u : StateSeries) :
    formalYDerivative u = rawFormalYDerivative u := by
  funext k
  unfold formalYDerivative
  let h : StateSeries := homogeneousOnly (k + 1) (u (k + 1))
  have hh : h (k + 1) = u (k + 1) := by
    unfold h homogeneousOnly
    rw [dif_pos rfl]
    ext v
    rfl
  have hd : u.derivSeries k = h.derivSeries k :=
    derivSeries_coeff_congr hh.symm
  unfold rawFormalYDerivative
  simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply]
  rw [hd]

lemma rawFormalYDerivative_coeff_congr
    {p q : StateSeries} {k : ℕ} (h : p (k + 1) = q (k + 1)) :
    rawFormalYDerivative p k = rawFormalYDerivative q k := by
  unfold rawFormalYDerivative
  simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply]
  rw [derivSeries_coeff_congr h]

/-- Multiplication by `y` is the Cauchy product with the sparse linear
series `ySeries`, on diagonal inputs. -/
theorem multiplyByY_apply_diag_eq_cauchy
    (d : StateSeries) (k : ℕ) (z : Domain) :
    multiplyByY d k (fun _ : Fin k => z) =
      ∑ i ∈ Finset.range (k + 1),
        (ContinuousLinearMap.lsmul ℝ ℝ :
          ℝ →L[ℝ] FirstOrderState →L[ℝ] FirstOrderState)
          (ySeries i (fun _ : Fin i => z))
          (d (k - i) (fun _ : Fin (k - i) => z)) := by
  cases k with
  | zero => simp [multiplyByY, ySeries, linearSeries]
  | succ k =>
      rw [multiplyByY_apply_diag]
      rw [Finset.sum_eq_single 1]
      · simp [ySeries, yProjection, linearSeries]
      · intro i hi hne
        have hi' : i < k + 2 := Finset.mem_range.mp hi
        rcases i with (_ | _ | i)
        · simp [ySeries, linearSeries]
        · exact (hne rfl).elim
        · simp [ySeries, linearSeries]
      · simp

/-- The coefficient-local Euler series is the ordinary sparse product of
`ySeries` with the full directional derivative series. -/
theorem formalEulerY_eq_multiplyByY_rawFormalYDerivative (u : StateSeries) :
    formalEulerY u = multiplyByY (rawFormalYDerivative u) := by
  funext k
  cases k with
  | zero => simp [formalEulerY, multiplyByY]
  | succ k =>
      unfold formalEulerY
      rw [multiplyByY_succ, multiplyByY_succ]
      have hh : homogeneousOnly (k + 1) (u (k + 1)) (k + 1) =
          u (k + 1) := by
        unfold homogeneousOnly
        rw [dif_pos rfl]
        ext v
        rfl
      rw [rawFormalYDerivative_coeff_congr hh]

/-- Linewise convergence of the sparse product `multiplyByY`. -/
theorem hasFPowerSeriesAt_multiplyByY_comp_scalarLine
    {D : Domain → FirstOrderState} {d : StateSeries}
    (hd : HasFPowerSeriesAt D d 0) (z : Domain) :
    HasFPowerSeriesAt
      (fun t : ℝ => (t • z).2 • D (t • z))
      ((multiplyByY d).compContinuousLinearMap (scalarLine z)) 0 := by
  have hy0 : HasFPowerSeriesAt (fun z : Domain => z.2) ySeries
      (scalarLine z 0) := by
    simpa only [scalarLine_apply, zero_smul] using hasFPowerSeriesAt_ySeries
  have hyline : HasFPowerSeriesAt
      ((fun z : Domain => z.2) ∘ scalarLine z)
      (ySeries.compContinuousLinearMap (scalarLine z)) 0 :=
    hy0.compContinuousLinearMap
  have hd0 : HasFPowerSeriesAt D d (scalarLine z 0) := by
    simpa only [scalarLine_apply, zero_smul] using hd
  have hdline : HasFPowerSeriesAt (D ∘ scalarLine z)
      (d.compContinuousLinearMap (scalarLine z)) 0 :=
    hd0.compContinuousLinearMap
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [hyline.eventually_hasSum, hdline.eventually_hasSum,
    Metric.eball_mem_nhds (0 : ℝ) hyline.radius_pos,
    Metric.eball_mem_nhds (0 : ℝ) hdline.radius_pos] with t hyt hdt hty htd
  have hynorm : Summable (fun n : ℕ =>
      ‖ySeries n (fun _ : Fin n => t • z)‖) := by
    refine (ySeries.compContinuousLinearMap (scalarLine z))
      |>.summable_norm_apply hty |>.congr ?_
    intro n
    rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
    apply congrArg norm
    congr 1
  have hdnorm : Summable (fun n : ℕ =>
      ‖d n (fun _ : Fin n => t • z)‖) := by
    refine (d.compContinuousLinearMap (scalarLine z))
      |>.summable_norm_apply htd |>.congr ?_
    intro n
    rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
    apply congrArg norm
    congr 1
  have hyt' : HasSum (fun n : ℕ =>
      ySeries n (fun _ : Fin n => t • z)) (t • z).2 := by
    have hx : HasSum (fun n : ℕ =>
        ySeries n (fun _ : Fin n => t • z))
        (((fun z : Domain => z.2) ∘ scalarLine z) (0 + t)) :=
      hyt.congr_fun (fun n => by
        rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
        congr 1)
    simpa only [Function.comp_apply, zero_add, scalarLine_apply] using hx
  have hdt' : HasSum (fun n : ℕ =>
      d n (fun _ : Fin n => t • z)) (D (t • z)) := by
    have hx : HasSum (fun n : ℕ =>
        d n (fun _ : Fin n => t • z))
        ((D ∘ scalarLine z) (0 + t)) :=
      hdt.congr_fun (fun n => by
        rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
        congr 1)
    simpa only [Function.comp_apply, zero_add, scalarLine_apply] using hx
  let B : ℝ →L[ℝ] FirstOrderState →L[ℝ] FirstOrderState :=
    ContinuousLinearMap.lsmul ℝ ℝ
  have hcauchy :=
    HasSum.continuousLinearMap_apply_cauchy_range_of_summable_norm
      B hyt' hdt' hynorm hdnorm
  have hmul : HasSum (fun k : ℕ =>
      multiplyByY d k (fun _ : Fin k => t • z))
      ((t • z).2 • D (t • z)) := by
    have hx : HasSum (fun k : ℕ =>
        multiplyByY d k (fun _ : Fin k => t • z))
        (B (t • z).2 (D (t • z))) :=
      hcauchy.congr_fun (fun k =>
        multiplyByY_apply_diag_eq_cauchy d k (t • z))
    simpa only [B, ContinuousLinearMap.lsmul_apply] using hx
  have hline : HasSum (fun k : ℕ =>
      ((multiplyByY d).compContinuousLinearMap (scalarLine z)) k
        (fun _ : Fin k => t))
      ((t • z).2 • D (t • z)) := by
    refine hmul.congr_fun ?_
    intro k
    rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
    congr 1
  simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    zero_add] using hline

/-- Any analytic FMS for the actual Euler field
`z.2 • fderiv U z yDirection` has the same homogeneous diagonal as
`formalEulerY u`. -/
theorem formalEulerY_diagonal_eq_of_hasFPowerSeriesAt
    {U : Domain → FirstOrderState} {u e : StateSeries}
    (hu : HasFPowerSeriesAt U u 0)
    (he : HasFPowerSeriesAt
      (fun z => z.2 • fderiv ℝ U z yDirection) e 0)
    (k : ℕ) (z : Domain) :
    e k (fun _ : Fin k => z) =
      formalEulerY u k (fun _ : Fin k => z) := by
  have he0 : HasFPowerSeriesAt
      (fun z => z.2 • fderiv ℝ U z yDirection) e (scalarLine z 0) := by
    simpa only [scalarLine_apply, zero_smul] using he
  have hel := he0.compContinuousLinearMap
  have hd := hasFPowerSeriesAt_rawFormalYDerivative hu
  have hm := hasFPowerSeriesAt_multiplyByY_comp_scalarLine hd z
  rw [← formalEulerY_eq_multiplyByY_rawFormalYDerivative] at hm
  have hel' : HasFPowerSeriesAt
      (fun t : ℝ => (t • z).2 • fderiv ℝ U (t • z) yDirection)
      (e.compContinuousLinearMap (scalarLine z)) 0 := by
    convert hel using 1
    funext t
    rfl
  have heq := hel'.eq_formalMultilinearSeries hm
  have hone := congrArg (fun p : FormalMultilinearSeries ℝ ℝ FirstOrderState =>
    p k (fun _ : Fin k => (1 : ℝ))) heq
  rw [FormalMultilinearSeries.compContinuousLinearMap_apply,
    FormalMultilinearSeries.compContinuousLinearMap_apply] at hone
  convert hone using 1 <;> congr 1 <;> funext i <;>
    simp only [Function.comp_apply, scalarLine_apply, one_smul]

/-! ## The reduced right-hand side -/

/-- The actual phase associated with a state field. -/
def actualPhase (U : Domain → FirstOrderState) (z : Domain) :
    FirstOrderPhase :=
  firstOrderPhase z.2 (U z 0) (U z 1)

/-- Pointwise analytic right-hand side of the reduced vector equation. -/
def actualReducedRHS
    (Nfun : FirstOrderPhase → FirstOrderOperator)
    (bfun : FirstOrderPhase → FirstOrderState)
    (U : Domain → FirstOrderState) (z : Domain) : FirstOrderState :=
  Matrix.mulVec (Nfun (actualPhase U z))
      (z.2 • fderiv ℝ U z yDirection) +
    bfun (actualPhase U z)

/-- The actual Euler field is analytic; this helper also retains one
specific Mathlib FMS representative for coefficient comparison. -/
theorem exists_hasFPowerSeriesAt_actualEuler
    {U : Domain → FirstOrderState} {u : StateSeries}
    (hu : HasFPowerSeriesAt U u 0) :
    ∃ e : StateSeries,
      HasFPowerSeriesAt
        (fun z => z.2 • fderiv ℝ U z yDirection) e 0 := by
  have hy := hasFPowerSeriesAt_ySeries
  have hd := hasFPowerSeriesAt_rawFormalYDerivative hu
  have hpair := hy.prod hd
  let B : ℝ →L[ℝ] FirstOrderState →L[ℝ] FirstOrderState :=
    ContinuousLinearMap.lsmul ℝ ℝ
  let φ : Domain → ℝ × FirstOrderState :=
    fun z => (z.2, fderiv ℝ U z yDirection)
  have hB := B.hasFPowerSeriesAt_bilinear (φ 0)
  have hc : HasFPowerSeriesAt
      ((fun q : ℝ × FirstOrderState => B q.1 q.2) ∘ φ)
      ((B.fpowerSeriesBilinear (φ 0)).comp
        (ySeries.prod (rawFormalYDerivative u))) 0 :=
    hB.comp hpair
  refine ⟨(B.fpowerSeriesBilinear (φ 0)).comp
    (ySeries.prod (rawFormalYDerivative u)), ?_⟩
  convert hc using 1
  funext z
  rfl

/-- Every analytic FMS representative of the actual reduced right-hand
side has the same diagonal homogeneous terms as `reducedRHS N b u`. -/
theorem reducedRHS_diagonal_eq_of_hasFPowerSeriesAt
    {Nfun : FirstOrderPhase → FirstOrderOperator}
    {bfun : FirstOrderPhase → FirstOrderState}
    {U : Domain → FirstOrderState}
    {N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator}
    {b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState}
    {u r : StateSeries}
    (hN : HasFPowerSeriesAt Nfun N 0)
    (hb : HasFPowerSeriesAt bfun b 0)
    (hu : HasFPowerSeriesAt U u 0)
    (hU0 : U 0 = 0)
    (hr : HasFPowerSeriesAt (actualReducedRHS Nfun bfun U) r 0)
    (k : ℕ) (z : Domain) :
    r k (fun _ : Fin k => z) =
      reducedRHS N b u k (fun _ : Fin k => z) := by
  have hphase := hasFPowerSeriesAt_phaseSeries hu
  have hphase0 : actualPhase U 0 = 0 := by
    simp [actualPhase, hU0, firstOrderPhase]
  have hN0 : HasFPowerSeriesAt Nfun N (actualPhase U 0) := by
    simpa only [hphase0] using hN
  have hb0 : HasFPowerSeriesAt bfun b (actualPhase U 0) := by
    simpa only [hphase0] using hb
  have hNcomp : HasFPowerSeriesAt (Nfun ∘ actualPhase U)
      (N.comp (phaseSeries u)) 0 := by
    exact hN0.comp hphase
  have hbcomp : HasFPowerSeriesAt (bfun ∘ actualPhase U)
      (b.comp (phaseSeries u)) 0 := by
    exact hb0.comp hphase
  obtain ⟨e, he⟩ := exists_hasFPowerSeriesAt_actualEuler hu
  have hsub := hr.sub hbcomp
  have haction : HasFPowerSeriesAt
      (fun z => Matrix.mulVec (Nfun (actualPhase U z))
        (z.2 • fderiv ℝ U z yDirection))
      (r - b.comp (phaseSeries u)) 0 := by
    apply hsub.congr
    filter_upwards [] with w
    change
      Matrix.mulVec (Nfun (actualPhase U w))
          (w.2 • fderiv ℝ U w yDirection) + bfun (actualPhase U w) -
        bfun (actualPhase U w) =
      Matrix.mulVec (Nfun (actualPhase U w))
        (w.2 • fderiv ℝ U w yDirection)
    exact add_sub_cancel_right _ _
  have hactdiag := formalAction_diagonal_eq_of_hasFPowerSeriesAt
    hNcomp he haction (fun w => rfl) k z
  have hsum :
      r k (fun _ : Fin k => z) =
        formalAction (N.comp (phaseSeries u)) e k (fun _ : Fin k => z) +
          (b.comp (phaseSeries u)) k (fun _ : Fin k => z) := by
    exact sub_eq_iff_eq_add.mp hactdiag
  rw [hsum]
  change
    formalAction (N.comp (phaseSeries u)) e k (fun _ : Fin k => z) +
        (b.comp (phaseSeries u)) k (fun _ : Fin k => z) =
      formalAction (N.comp (phaseSeries u)) (formalEulerY u) k
          (fun _ : Fin k => z) +
        (b.comp (phaseSeries u)) k (fun _ : Fin k => z)
  congr 1
  rw [CKFormalActionEvaluation.formalAction_apply_diag,
    CKFormalActionEvaluation.formalAction_apply_diag]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact formalEulerY_diagonal_eq_of_hasFPowerSeriesAt hu he (k - i) z

/-! ## The `x` derivative and ordinary polar coefficients -/

/-- Coordinate direction normal to the Cauchy axis. -/
def xDirection : Domain := (1, 0)

/-- Formal derivative in the fixed `x` direction. -/
def rawFormalXDerivative (u : StateSeries) : StateSeries :=
  (ContinuousLinearMap.apply ℝ FirstOrderState xDirection)
    |>.compFormalMultilinearSeries u.derivSeries

/-- Differentiating an analytic state germ in the fixed `x` direction has
the formal series `rawFormalXDerivative`. -/
theorem hasFPowerSeriesAt_rawFormalXDerivative
    {U : Domain → FirstOrderState} {u : StateSeries}
    (hu : HasFPowerSeriesAt U u 0) :
    HasFPowerSeriesAt
      (fun z => fderiv ℝ U z xDirection)
      (rawFormalXDerivative u) 0 := by
  rcases hu with ⟨r, hu⟩
  refine ⟨r, ?_⟩
  have hd := hu.fderiv
  have he := (ContinuousLinearMap.apply ℝ FirstOrderState xDirection)
    |>.comp_hasFPowerSeriesOnBall hd
  change HasFPowerSeriesOnBall
    ((ContinuousLinearMap.apply ℝ FirstOrderState xDirection) ∘
      fderiv ℝ U)
    (rawFormalXDerivative u) 0 r at he
  convert he using 1
  funext z
  rfl

/-- Expanded insertion formula for one homogeneous `x` derivative. -/
theorem rawFormalXDerivative_apply_diag
    (u : StateSeries) (k : ℕ) (z : Domain) :
    rawFormalXDerivative u k (fun _ : Fin k => z) =
      ∑ s : {s : Finset (Fin (1 + k)) // s.card = k},
        u (1 + k)
          (s.1.piecewise (fun _ => z) (fun _ => xDirection)) := by
  unfold rawFormalXDerivative FormalMultilinearSeries.derivSeries
  simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_coe,
    Function.comp_apply, ContinuousLinearMap.apply_apply,
    continuousMultilinearCurryFin1_apply,
    FormalMultilinearSeries.changeOriginSeries, sum_apply]
  apply Finset.sum_congr rfl
  intro s hs
  exact FormalMultilinearSeries.changeOriginSeriesTerm_apply
    u 1 k s.1 s.2 z xDirection

/-- The finite homogeneous series has exactly its single advertised sum. -/
private lemma homogeneousOnly_sum
    (q : Domain [×k]→L[ℝ] FirstOrderState) (z : Domain) :
    (homogeneousOnly k q).sum z = q (fun _ : Fin k => z) := by
  unfold FormalMultilinearSeries.sum
  rw [tsum_eq_single k]
  · simp [homogeneousOnly]
  · intro l hl
    simp [homogeneousOnly, Ne.symm hl]

/-- A finite-support witness for a homogeneous-only series. -/
private lemma homogeneousOnly_finite
    (q : Domain [×k]→L[ℝ] FirstOrderState) :
    ∀ d, k + 1 ≤ d → homogeneousOnly k q d = 0 := by
  intro d hd
  simp only [homogeneousOnly]
  split
  next h => omega
  next => rfl

/-- A coefficient-local `x` derivative is the derivative of the associated
finite homogeneous polynomial, evaluated in `xDirection`. -/
private lemma rawFormalXDerivative_homogeneousOnly_apply_diag
    (q : Domain [×(k + 1)]→L[ℝ] FirstOrderState)
    (z : Domain) :
    rawFormalXDerivative (homogeneousOnly (k + 1) q) k
        (fun _ : Fin k => z) =
      (continuousMultilinearCurryFin1 ℝ Domain FirstOrderState
        ((homogeneousOnly (k + 1) q).changeOrigin z 1)) xDirection := by
  unfold rawFormalXDerivative
  simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply',
    ContinuousLinearMap.apply_apply, FormalMultilinearSeries.derivSeries,
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

/-- Differentiation of the degree-`k+1` diagonal polynomial along the
affine line `(x,1)` is represented by `rawFormalXDerivative`. -/
private lemma hasDerivAt_homogeneous_diagonal_x
    (q : Domain [×(k + 1)]→L[ℝ] FirstOrderState)
    (i : Fin 2) (x : ℝ) :
    HasDerivAt
      (fun t : ℝ => (ContinuousLinearMap.proj (R := ℝ) i)
        (q (fun _ : Fin (k + 1) => (t, 1))))
      ((ContinuousLinearMap.proj (R := ℝ) i)
        (rawFormalXDerivative (homogeneousOnly (k + 1) q) k
          (fun _ : Fin k => (x, 1)))) x := by
  let p : StateSeries := homogeneousOnly (k + 1) q
  have hpfinite : ∀ d, k + 2 ≤ d → p d = 0 := by
    exact homogeneousOnly_finite q
  have hp := p.hasFiniteFPowerSeriesOnBall_of_finite hpfinite
  have hF := hp.toHasFPowerSeriesOnBall.hasFDerivAt
    (y := ((x, 1) : Domain)) (by simp)
  have hF' : HasFDerivAt p.sum
      (continuousMultilinearCurryFin1 ℝ Domain FirstOrderState
        (p.changeOrigin (x, 1) 1)) (x, 1) := by
    simpa using hF
  have hslice := hF'.comp_hasDerivAt x
    (hasFDerivAt_prodMk_left x (1 : ℝ)).hasDerivAt
  have hcomponent :=
    (ContinuousLinearMap.proj (R := ℝ) i).hasFDerivAt.comp_hasDerivAt
      x hslice
  have hpSum : (fun t : ℝ => p.sum (t, 1)) =
      (fun t : ℝ => q (fun _ : Fin (k + 1) => (t, 1))) := by
    funext t
    exact homogeneousOnly_sum _ _
  have hcomponent' : HasDerivAt
      (fun t : ℝ => (ContinuousLinearMap.proj (R := ℝ) i)
        (q (fun _ : Fin (k + 1) => (t, 1))))
      ((ContinuousLinearMap.proj (R := ℝ) i)
        ((continuousMultilinearCurryFin1 ℝ Domain FirstOrderState
          (p.changeOrigin (x, 1) 1)) xDirection)) x := by
    simpa only [Function.comp_def, ContinuousLinearMap.inl_apply,
      one_smul, xDirection, hpSum] using hcomponent
  rw [rawFormalXDerivative_homogeneousOnly_apply_diag]
  exact hcomponent'

/-- The diagonal polynomial of the formal `x` derivative is the ordinary
polynomial derivative of the next homogeneous diagonal polynomial. -/
theorem scalarDiagonalPolynomial_rawFormalXDerivative
    (u : StateSeries) (i : Fin 2) (k : ℕ) :
    scalarDiagonalPolynomial (componentSeries (rawFormalXDerivative u) i) k =
      (scalarDiagonalPolynomial (componentSeries u i) (k + 1)).derivative := by
  apply Polynomial.funext
  intro x
  rw [eval_scalarDiagonalPolynomial, componentSeries_apply]
  let q := u (k + 1)
  let h : StateSeries := homogeneousOnly (k + 1) q
  have hh : h (k + 1) = u (k + 1) := by
    unfold h q homogeneousOnly
    rw [dif_pos rfl]
    ext v
    rfl
  have hxcoeff : rawFormalXDerivative h k = rawFormalXDerivative u k := by
    unfold rawFormalXDerivative
    simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply]
    rw [derivSeries_coeff_congr hh]
  have hslice := hasDerivAt_homogeneous_diagonal_x q i x
  have hslice' : HasDerivAt
      (fun t : ℝ => (ContinuousLinearMap.proj (R := ℝ) i)
        (u (k + 1) (fun _ : Fin (k + 1) => (t, 1))))
      ((ContinuousLinearMap.proj (R := ℝ) i)
        (rawFormalXDerivative u k (fun _ : Fin k => (x, 1)))) x := by
    simpa only [q, h, hxcoeff] using hslice
  have hpoly :=
    (scalarDiagonalPolynomial (componentSeries u i) (k + 1)).hasDerivAt x
  have hpoly' : HasDerivAt
      (fun t : ℝ => (ContinuousLinearMap.proj (R := ℝ) i)
        (u (k + 1) (fun _ : Fin (k + 1) => (t, 1))))
      (Polynomial.eval x
        (scalarDiagonalPolynomial (componentSeries u i) (k + 1)).derivative) x := by
    apply hpoly.congr_of_eventuallyEq
    filter_upwards [] with t
    rw [eval_scalarDiagonalPolynomial, componentSeries_apply,
      ContinuousLinearMap.proj_apply]
  simpa only [ContinuousLinearMap.proj_apply] using hslice'.unique hpoly'

/-- Exact ordinary polar-coefficient formula for one `x` derivative. -/
theorem polarCoefficient_rawFormalXDerivative
    (u : StateSeries) (m n : ℕ) :
    polarCoefficient (rawFormalXDerivative u) m n =
      ((m + 1 : ℕ) : ℝ) • polarCoefficient u (m + 1) n := by
  funext i
  simp only [Pi.smul_apply]
  rw [formal_polarCoefficient_eq_evaluation_polarCoefficient,
    formal_polarCoefficient_eq_evaluation_polarCoefficient,
    ← polarCoefficient_componentSeries,
    ← polarCoefficient_componentSeries]
  have hm : m ≤ m + n := Nat.le_add_right m n
  have hms : m + 1 ≤ m + n + 1 := Nat.succ_le_succ hm
  calc
    CKPolarEvaluation.polarCoefficient
        (componentSeries (rawFormalXDerivative u) i) m n =
        (scalarDiagonalPolynomial
          (componentSeries (rawFormalXDerivative u) i) (m + n)).coeff m := by
      symm
      simpa only [Nat.add_sub_cancel_left] using
        coeff_scalarDiagonalPolynomial
          (componentSeries (rawFormalXDerivative u) i) hm
    _ = ((scalarDiagonalPolynomial (componentSeries u i)
          (m + n + 1)).derivative).coeff m := by
      rw [scalarDiagonalPolynomial_rawFormalXDerivative]
    _ = (scalarDiagonalPolynomial (componentSeries u i)
          (m + n + 1)).coeff (m + 1) * (m + 1) := by
      rw [Polynomial.coeff_derivative]
    _ = ((m + 1 : ℕ) : ℝ) •
        CKPolarEvaluation.polarCoefficient
          (componentSeries u i) (m + 1) n := by
      rw [coeff_scalarDiagonalPolynomial _ hms]
      have hsub : m + n + 1 - (m + 1) = n := by omega
      rw [hsub]
      simp only [Nat.cast_add, Nat.cast_one, smul_eq_mul]
      ring

/-- On homogeneous diagonal evaluations, differentiating the canonical
bivariate FMS is exactly the canonical series of the ordinary derivative
array. -/
theorem rawFormalXDerivative_stateBivariateFMS_apply_diag
    (a : BivariateStateCoeff) (k : ℕ) (x y : ℝ) :
    rawFormalXDerivative (stateBivariateFMS a) k
        (fun _ : Fin k => (x, y)) =
      stateBivariateFMS (xDerivativeCoefficientArray a) k
        (fun _ : Fin k => (x, y)) := by
  have harr :
      polarCoefficientArray (rawFormalXDerivative (stateBivariateFMS a)) =
        xDerivativeCoefficientArray a := by
    funext m n
    change CKPolarEvaluation.polarCoefficient
        (rawFormalXDerivative (stateBivariateFMS a)) m n =
      ((m + 1 : ℕ) : ℝ) • a (m + 1) n
    rw [← formal_polarCoefficient_eq_evaluation_polarCoefficient,
      polarCoefficient_rawFormalXDerivative,
      polarCoefficient_stateBivariateFMS]
  rw [← harr]
  exact (stateBivariateFMS_polarCoefficientArray_apply_diag
    (rawFormalXDerivative (stateBivariateFMS a)) k x y).symm

/-! ## Diagonal invariance of the reduced formal right-hand side -/

/-- The finite homogeneous `y` derivative is the derivative of its
homogeneous polynomial in `yDirection`. -/
private lemma rawFormalYDerivative_homogeneousOnly_apply_diag_local
    (q : Domain [×(k + 1)]→L[ℝ] FirstOrderState)
    (z : Domain) :
    rawFormalYDerivative (homogeneousOnly (k + 1) q) k
        (fun _ : Fin k => z) =
      (continuousMultilinearCurryFin1 ℝ Domain FirstOrderState
        ((homogeneousOnly (k + 1) q).changeOrigin z 1)) yDirection := by
  unfold rawFormalYDerivative
  simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply',
    ContinuousLinearMap.apply_apply, FormalMultilinearSeries.derivSeries,
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

/-- Directional differentiation of a finite homogeneous diagonal
polynomial in the `y` variable. -/
private lemma hasDerivAt_homogeneous_diagonal_y
    (q : Domain [×(k + 1)]→L[ℝ] FirstOrderState)
    (x y : ℝ) :
    HasDerivAt
      (fun t : ℝ => q (fun _ : Fin (k + 1) => (x, t)))
      (rawFormalYDerivative (homogeneousOnly (k + 1) q) k
        (fun _ : Fin k => (x, y))) y := by
  let p : StateSeries := homogeneousOnly (k + 1) q
  have hpfinite : ∀ d, k + 2 ≤ d → p d = 0 := by
    exact homogeneousOnly_finite q
  have hp := p.hasFiniteFPowerSeriesOnBall_of_finite hpfinite
  have hF := hp.toHasFPowerSeriesOnBall.hasFDerivAt
    (y := ((x, y) : Domain)) (by simp)
  have hF' : HasFDerivAt p.sum
      (continuousMultilinearCurryFin1 ℝ Domain FirstOrderState
        (p.changeOrigin (x, y) 1)) (x, y) := by
    simpa using hF
  have hslice := hF'.comp_hasDerivAt y
    (hasFDerivAt_prodMk_right x y).hasDerivAt
  have hpSum : (fun t : ℝ => p.sum (x, t)) =
      (fun t : ℝ => q (fun _ : Fin (k + 1) => (x, t))) := by
    funext t
    exact homogeneousOnly_sum _ _
  have hslice' : HasDerivAt
      (fun t : ℝ => q (fun _ : Fin (k + 1) => (x, t)))
      ((continuousMultilinearCurryFin1 ℝ Domain FirstOrderState
        (p.changeOrigin (x, y) 1)) yDirection) y := by
    simpa only [Function.comp_def, ContinuousLinearMap.inr_apply,
      one_smul, yDirection, hpSum] using hslice
  rw [rawFormalYDerivative_homogeneousOnly_apply_diag_local]
  exact hslice'

/-- The coefficient-local Euler construction depends only on homogeneous
diagonal values, despite using nonsymmetric multilinear representatives. -/
theorem formalEulerY_apply_diag_congr
    {u v : StateSeries} (huv : DiagonallyEquivalent u v)
    (k : ℕ) (z : Domain) :
    formalEulerY u k (fun _ : Fin k => z) =
      formalEulerY v k (fun _ : Fin k => z) := by
  cases k with
  | zero => simp [formalEulerY, multiplyByY]
  | succ k =>
      unfold formalEulerY
      rw [multiplyByY_apply_diag, multiplyByY_apply_diag]
      congr 1
      have hu := hasDerivAt_homogeneous_diagonal_y
        (u (k + 1)) z.1 z.2
      have hv := hasDerivAt_homogeneous_diagonal_y
        (v (k + 1)) z.1 z.2
      have hv' : HasDerivAt
          (fun t : ℝ =>
            u (k + 1) (fun _ : Fin (k + 1) => (z.1, t)))
          (rawFormalYDerivative
            (homogeneousOnly (k + 1) (v (k + 1))) k
            (fun _ : Fin k => z)) z.2 := by
        apply hv.congr_of_eventuallyEq
        filter_upwards [] with t
        exact huv (k + 1) (z.1, t)
      exact hu.unique hv'

/-- The formal phase construction respects homogeneous diagonal
equivalence of state series. -/
theorem phaseSeries_diagonallyEquivalent
    {u v : StateSeries} (huv : DiagonallyEquivalent u v) :
    DiagonallyEquivalent (phaseSeries u) (phaseSeries v) := by
  intro k z
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact congrFun (huv k z) j

/-- The complete reduced formal right-hand side is invariant under
homogeneous diagonal canonicalization of the state FMS. -/
theorem reducedRHS_diagonallyEquivalent
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    {u v : StateSeries} (huv : DiagonallyEquivalent u v) :
    DiagonallyEquivalent (reducedRHS N b u) (reducedRHS N b v) := by
  have hphase := phaseSeries_diagonallyEquivalent huv
  have hN := comp_diagonallyEquivalent_inner N hphase
  have hb := comp_diagonallyEquivalent_inner b hphase
  have heuler : DiagonallyEquivalent (formalEulerY u) (formalEulerY v) :=
    fun k z => formalEulerY_apply_diag_congr huv k z
  have haction : DiagonallyEquivalent
      (formalAction (N.comp (phaseSeries u)) (formalEulerY u))
      (formalAction (N.comp (phaseSeries v)) (formalEulerY v)) := by
    exact formalActionOn_diagonallyEquivalent hN heuler
  intro k z
  exact congrArg₂ (fun x y : FirstOrderState => x + y)
    (haction k z) (hb k z)

/-- Polar coefficients are invariants of homogeneous diagonal
equivalence. -/
theorem polarCoefficient_eq_of_diagonallyEquivalent
    {p q : StateSeries} (hpq : DiagonallyEquivalent p q)
    (m n : ℕ) :
    polarCoefficient p m n = polarCoefficient q m n := by
  have hz := state_polarCoefficient_eq_zero_of_apply_diag_eq_zero
    (p - q) (fun k z => by
      change p k (fun _ : Fin k => z) - q k (fun _ : Fin k => z) = 0
      rw [hpq k z, sub_self]) m n
  rw [polarCoefficient_sub, sub_eq_zero] at hz
  exact hz

/-- Replacing an arbitrary state FMS by the canonical FMS of its polar
coefficients does not change any reduced-RHS polar coefficient. -/
theorem reducedRHSPolarCoefficient_eq_reducedArrayRHS
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (u : StateSeries) (m n : ℕ) :
    reducedRHSPolarCoefficient N b u m n =
      reducedArrayRHS N b (polarCoefficientArray u) m n := by
  have hcanon : DiagonallyEquivalent u
      (stateBivariateFMS (polarCoefficientArray u)) := by
    intro k z
    exact (stateBivariateFMS_polarCoefficientArray_apply_diag
      u k z.1 z.2).symm
  exact polarCoefficient_eq_of_diagonallyEquivalent
    (reducedRHS_diagonallyEquivalent N b hcanon) m n

/-! ## From the actual reduced PDE to the exact recurrence -/

/-- An analytic germ satisfying the actual reduced vector equation near the
origin has polar coefficients satisfying the exact integrated recurrence.
No symmetry of the supplied FMS representative is assumed. -/
theorem satisfiesReducedArrayRecurrence_of_eventuallyEq_reducedPDE
    {Nfun : FirstOrderPhase → FirstOrderOperator}
    {bfun : FirstOrderPhase → FirstOrderState}
    {U : Domain → FirstOrderState}
    {N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator}
    {b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState}
    {u : StateSeries}
    (hN : HasFPowerSeriesAt Nfun N 0)
    (hb : HasFPowerSeriesAt bfun b 0)
    (hu : HasFPowerSeriesAt U u 0)
    (hU0 : U 0 = 0)
    (hpde : (fun z => fderiv ℝ U z xDirection) =ᶠ[nhds 0]
      actualReducedRHS Nfun bfun U) :
    SatisfiesReducedArrayRecurrence N b (polarCoefficientArray u) := by
  have hx := hasFPowerSeriesAt_rawFormalXDerivative hu
  have hr : HasFPowerSeriesAt (actualReducedRHS Nfun bfun U)
      (rawFormalXDerivative u) 0 := hx.congr hpde
  have hdiag : DiagonallyEquivalent (rawFormalXDerivative u)
      (reducedRHS N b u) := by
    intro k z
    exact reducedRHS_diagonal_eq_of_hasFPowerSeriesAt
      hN hb hu hU0 hr k z
  intro m n
  unfold reducedNextXCoefficient
  have hcoefficient :
      ((m + 1 : ℕ) : ℝ) • polarCoefficient u (m + 1) n =
        reducedArrayRHS N b (polarCoefficientArray u) m n := by
    calc
      ((m + 1 : ℕ) : ℝ) • polarCoefficient u (m + 1) n =
          polarCoefficient (rawFormalXDerivative u) m n :=
        (polarCoefficient_rawFormalXDerivative u m n).symm
      _ = reducedRHSPolarCoefficient N b u m n := by
        exact polarCoefficient_eq_of_diagonallyEquivalent hdiag m n
      _ = reducedArrayRHS N b (polarCoefficientArray u) m n :=
        reducedRHSPolarCoefficient_eq_reducedArrayRHS N b u m n
  rw [← hcoefficient, smul_smul]
  have hm : (((m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [inv_mul_cancel₀ hm, one_smul]
  exact (formal_polarCoefficient_eq_evaluation_polarCoefficient
    u (m + 1) n).symm

/-- Stress-tensor specialization.  The quantitative majorants chosen in the
formal system supply the two coefficient germs automatically, while the
Cauchy data supply the zero base state. -/
theorem actualFirstOrderState_satisfiesReducedArrayRecurrence
    (P : Params) {gamma : ℝ → ℝ → ℝ} {radius : ℝ}
    {u : StateSeries}
    (hu : HasFPowerSeriesAt (actualFirstOrderState gamma) u 0)
    (hdata : HasCauchyDataOn gamma radius) (hradius : 0 < radius)
    (hpde :
      (fun z => fderiv ℝ (actualFirstOrderState gamma) z xDirection) =ᶠ[nhds 0]
        actualReducedRHS (firstOrderPrincipalArray P)
          (firstOrderSourceVector P) (actualFirstOrderState gamma)) :
    SatisfiesReducedArrayRecurrence
      (firstOrderPrincipalOriginMajorant P).series
      (firstOrderSourceOriginMajorant P).series
      (polarCoefficientArray u) := by
  have hN : HasFPowerSeriesAt (firstOrderPrincipalArray P)
      (firstOrderPrincipalOriginMajorant P).series 0 := by
    simpa only [firstOrderOrigin] using
      (firstOrderPrincipalOriginMajorant P).hasFPowerSeriesOnBall.hasFPowerSeriesAt
  have hb : HasFPowerSeriesAt (firstOrderSourceVector P)
      (firstOrderSourceOriginMajorant P).series 0 := by
    simpa only [firstOrderOrigin] using
      (firstOrderSourceOriginMajorant P).hasFPowerSeriesOnBall.hasFPowerSeriesAt
  have hU0 : actualFirstOrderState gamma 0 = 0 := by
    apply actualFirstOrderState_zero_on_cauchyAxis_of_hasCauchyDataOn hdata
    simpa only [abs_zero] using hradius
  exact satisfiesReducedArrayRecurrence_of_eventuallyEq_reducedPDE
    hN hb hu hU0 hpde

end

end CKAnalyticCompetitorRecurrence
end StressTensor
