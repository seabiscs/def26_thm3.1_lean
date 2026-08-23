import StressTensor.CKFirstOrderAnalyticData
import StressTensor.CKFMSCompositionMajorant
import StressTensor.CKAnalyticEvaluation
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Formal coefficient solution of the reduced first-order system

This file formalizes the homogeneous algebra behind

`U_x = y N(y,U) U_y + b(y,U)`.

It builds the coordinate and phase series, formal `y` differentiation,
multiplication by `y`, formal matrix action, and analytic substitution.  The
central causality theorem says that the homogeneous right-hand side in total
degree `k` only depends on the unknown through degree `k`.

The second half exposes ordinary bivariate coefficients by polarizing the
homogeneous maps.  Formal integration divides by the new `x` degree `m+1`
(not by total degree), and a strong recursion on total degree constructs the
unique formal coefficient array.  The construction is finally specialized
to the Taylor germs of the actual reduced stress-tensor coefficients.

This is a formal existence-and-uniqueness theorem.  Convergence of the
resulting coefficient array is a separate majorant step.
-/

namespace StressTensor
namespace CKFirstOrderFormalSystem

noncomputable section

abbrev Domain := ℝ × ℝ
abbrev StateSeries := FormalMultilinearSeries ℝ Domain FirstOrderState
abbrev OperatorSeries := FormalMultilinearSeries ℝ Domain FirstOrderOperator

noncomputable def operatorActionCLM :
    FirstOrderOperator →L[ℝ] FirstOrderState →L[ℝ] FirstOrderState :=
  (LinearMap.toContinuousLinearMap (𝕜 := ℝ))
    (((LinearMap.toContinuousLinearMap (𝕜 := ℝ) :
        (FirstOrderState →ₗ[ℝ] FirstOrderState) ≃ₗ[ℝ]
          FirstOrderState →L[ℝ] FirstOrderState)).toLinearMap.comp
      (Matrix.mulVecBilin ℝ ℝ))

@[simp] lemma operatorActionCLM_apply
    (A : FirstOrderOperator) (u : FirstOrderState) :
    operatorActionCLM A u = Matrix.mulVec A u := by
  rfl

noncomputable def splitAction {i j : ℕ}
    (A : Domain [×i]→L[ℝ] FirstOrderOperator)
    (u : Domain [×j]→L[ℝ] FirstOrderState) :
    ContinuousMultilinearMap ℝ (fun _ : Fin i ⊕ Fin j => Domain) FirstOrderState :=
  (((ContinuousLinearMap.compContinuousMultilinearMapL ℝ
      (fun _ : Fin j => Domain) FirstOrderState FirstOrderState).flip u)
    |>.compContinuousMultilinearMap
      (operatorActionCLM.compContinuousMultilinearMap A)).uncurrySum

noncomputable def splitActionFin {i j : ℕ}
    (A : Domain [×i]→L[ℝ] FirstOrderOperator)
    (u : Domain [×j]→L[ℝ] FirstOrderState) :
    Domain [×(i + j)]→L[ℝ] FirstOrderState :=
  (splitAction A u).domDomCongr finSumFinEquiv

@[simp] lemma splitActionFin_apply {i j : ℕ}
    (A : Domain [×i]→L[ℝ] FirstOrderOperator)
    (u : Domain [×j]→L[ℝ] FirstOrderState)
    (v : Fin (i+j) → Domain) :
    splitActionFin A u v =
      operatorActionCLM
        (A (v ∘ (finSumFinEquiv ∘ Sum.inl)))
        (u (v ∘ (finSumFinEquiv ∘ Sum.inr))) := by
  rfl

noncomputable def actionHomogeneous (A : OperatorSeries) (u : StateSeries)
    (k i : ℕ) : Domain [×k]→L[ℝ] FirstOrderState :=
  if hi : i ≤ k then
    (splitActionFin (A i) (u (k - i))).domDomCongr
      (finCongr (Nat.add_sub_of_le hi))
  else 0

noncomputable def formalAction (A : OperatorSeries) (u : StateSeries) : StateSeries :=
  fun k => ∑ i ∈ Finset.range (k + 1), actionHomogeneous A u k i

def xProjection : Domain →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
def yProjection : Domain →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ

noncomputable def linearSeries (l : Domain →L[ℝ] ℝ) :
    FormalMultilinearSeries ℝ Domain ℝ
  | 0 => 0
  | 1 => (continuousMultilinearCurryFin1 ℝ Domain ℝ).symm l
  | _ + 2 => 0

def xSeries := linearSeries xProjection
def ySeries := linearSeries yProjection

def yDirection : Domain := (0, 1)

/-- Keep one homogeneous coefficient and set all other coefficients to zero. -/
noncomputable def homogeneousOnly (k : ℕ)
    (q : Domain [×k]→L[ℝ] FirstOrderState) : StateSeries :=
  fun n => if h : k = n then q.domDomCongr (finCongr h) else 0

/-- Directional `y` derivative of a whole formal series. -/
noncomputable def rawFormalYDerivative (u : StateSeries) : StateSeries :=
  (ContinuousLinearMap.apply ℝ FirstOrderState yDirection)
    |>.compFormalMultilinearSeries u.derivSeries

/-- Formal `y` derivative, represented coefficient-locally.  Isolating the
only homogeneous input used at degree `k` makes coefficient causality
definitionally transparent. -/
noncomputable def formalYDerivative (u : StateSeries) : StateSeries :=
  fun k => rawFormalYDerivative (homogeneousOnly (k + 1) (u (k + 1))) k

noncomputable def multiplyByY (u : StateSeries) : StateSeries
  | 0 => 0
  | k + 1 => ContinuousLinearMap.uncurryLeft (yProjection.smulRight (u k))

@[simp] lemma multiplyByY_zero (u : StateSeries) : multiplyByY u 0 = 0 := rfl

@[simp] lemma multiplyByY_succ (u : StateSeries) (k : ℕ) :
    multiplyByY u (k+1) =
      ContinuousLinearMap.uncurryLeft (yProjection.smulRight (u k)) := rfl

lemma multiplyByY_apply_diag (u : StateSeries) (k : ℕ) (p : Domain) :
    multiplyByY u (k+1) (fun _ => p) = p.2 • u k (fun _ => p) := by
  rw [multiplyByY_succ, ContinuousLinearMap.uncurryLeft_apply]
  change p.2 • u k (Fin.tail (fun _ : Fin (k+1) => p)) =
    p.2 • u k (fun _ : Fin k => p)
  congr 2

lemma formalYDerivative_coeff_congr {u v : StateSeries} {k : ℕ}
    (h : u (k+1) = v (k+1)) :
    formalYDerivative u k = formalYDerivative v k := by
  unfold formalYDerivative
  rw [h]

noncomputable def stateComponent (i : Fin 2) (u : StateSeries) :
    FormalMultilinearSeries ℝ Domain ℝ :=
  (ContinuousLinearMap.proj i).compFormalMultilinearSeries u

noncomputable def phaseSeries (u : StateSeries) :
    FormalMultilinearSeries ℝ Domain FirstOrderPhase :=
  FormalMultilinearSeries.pi fun i =>
    Fin.cases ySeries (fun j : Fin 2 => stateComponent j u) i

lemma multiplyByY_coeff_congr {u v : StateSeries} {k : ℕ}
    (h : u k = v k) : multiplyByY u (k + 1) = multiplyByY v (k + 1) := by
  rw [multiplyByY_succ, multiplyByY_succ, h]

/-- The Euler derivative `y ∂y`, represented coefficient-locally. -/
noncomputable def formalEulerY (u : StateSeries) : StateSeries :=
  fun k => multiplyByY
    (rawFormalYDerivative (homogeneousOnly k (u k))) k

lemma formalEulerY_coeff_congr {u v : StateSeries} {k : ℕ}
    (h : u k = v k) :
    formalEulerY u k = formalEulerY v k := by
  unfold formalEulerY
  rw [h]

lemma stateComponent_coeff_congr (i : Fin 2) {u v : StateSeries} {k : ℕ}
    (h : u k = v k) : stateComponent i u k = stateComponent i v k := by
  unfold stateComponent
  simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply]
  rw [h]

lemma phaseSeries_coeff_congr {u v : StateSeries} {k : ℕ}
    (h : u k = v k) : phaseSeries u k = phaseSeries v k := by
  ext p i
  simp only [phaseSeries, FormalMultilinearSeries.pi,
    ContinuousMultilinearMap.pi_apply]
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact DFunLike.congr_fun (stateComponent_coeff_congr j h) p

/-- Agreement of formal coefficients through total degree `k`. -/
def AgreeUpTo (k : ℕ) (u v : StateSeries) : Prop :=
  ∀ n, n ≤ k → u n = v n

lemma phaseSeries_agreeUpTo {u v : StateSeries} {k : ℕ}
    (h : AgreeUpTo k u v) (n : ℕ) (hn : n ≤ k) :
    phaseSeries u n = phaseSeries v n :=
  phaseSeries_coeff_congr (h n hn)

lemma comp_coeff_congr_of_forall_le
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (q : FormalMultilinearSeries ℝ FirstOrderPhase G)
    {p r : FormalMultilinearSeries ℝ Domain FirstOrderPhase} {k : ℕ}
    (h : ∀ n, n ≤ k → p n = r n) :
    q.comp p k = q.comp r k := by
  unfold FormalMultilinearSeries.comp
  apply Finset.sum_congr rfl
  intro c hc
  ext z
  simp only [FormalMultilinearSeries.compAlongComposition_apply]
  congr 1
  funext i
  unfold FormalMultilinearSeries.applyComposition
  rw [h _ (Composition.blocksFun_le c i)]

lemma phase_comp_coeff_congr
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (q : FormalMultilinearSeries ℝ FirstOrderPhase G)
    {u v : StateSeries} {k : ℕ} (h : AgreeUpTo k u v) :
    q.comp (phaseSeries u) k = q.comp (phaseSeries v) k :=
  comp_coeff_congr_of_forall_le q (phaseSeries_agreeUpTo h)

lemma actionHomogeneous_coeff_congr
    {A B : OperatorSeries} {u v : StateSeries} {k i : ℕ}
    (hA : ∀ n, n ≤ k → A n = B n)
    (hu : AgreeUpTo k u v) :
    actionHomogeneous A u k i = actionHomogeneous B v k i := by
  unfold actionHomogeneous
  split
  next hi =>
    rw [hA i hi, hu (k - i) (Nat.sub_le k i)]
  next hi => rfl

lemma formalAction_coeff_congr
    {A B : OperatorSeries} {u v : StateSeries} {k : ℕ}
    (hA : ∀ n, n ≤ k → A n = B n)
    (hu : AgreeUpTo k u v) :
    formalAction A u k = formalAction B v k := by
  unfold formalAction
  apply Finset.sum_congr rfl
  intro i hi
  exact actionHomogeneous_coeff_congr hA hu

/-- The formal right-hand side of the reduced Fuchsian system
`U_x = y N(y,U) U_y + b(y,U)`.

The factor `y` is grouped with `U_y`; over `ℝ`, this is equivalent to the
displayed scalar multiplication before the matrix action. -/
noncomputable def reducedRHS
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (u : StateSeries) : StateSeries :=
  formalAction (N.comp (phaseSeries u))
      (formalEulerY u) +
    b.comp (phaseSeries u)

/-- The degree-`k` reduced right-hand side is causal: it only uses the
coefficients of the unknown state through degree `k`. -/
theorem reducedRHS_coeff_causal
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    {u v : StateSeries} {k : ℕ} (h : AgreeUpTo k u v) :
    reducedRHS N b u k = reducedRHS N b v k := by
  have hprincipal : ∀ n, n ≤ k →
      N.comp (phaseSeries u) n = N.comp (phaseSeries v) n := by
    intro n hn
    exact phase_comp_coeff_congr N (fun m hm => h m (hm.trans hn))
  have heuler : AgreeUpTo k
      (formalEulerY u) (formalEulerY v) := by
    intro n hn
    exact formalEulerY_coeff_congr (h n hn)
  have haction := formalAction_coeff_congr hprincipal heuler
  have hsource := phase_comp_coeff_congr b h
  change
    formalAction (N.comp (phaseSeries u))
          (formalEulerY u) k +
        b.comp (phaseSeries u) k =
      formalAction (N.comp (phaseSeries v))
          (formalEulerY v) k +
        b.comp (phaseSeries v) k
  exact congrArg₂ (· + ·) haction hsource

/-- Feed the `x`-axis vector into the slots in `s`, and the `y`-axis vector
into all remaining slots. -/
def polarSlotInput (k : ℕ) (s : Finset (Fin k)) : Fin k → Domain :=
  fun i => if i ∈ s then (1, 0) else (0, 1)

/-- The ordinary coefficient of `x^m y^n` represented by a homogeneous FMS.
For a nonsymmetric multilinear representative, every choice of the `m`
`x`-slots is summed; this is exactly the coefficient obtained by diagonal
evaluation and multilinear expansion. -/
noncomputable def polarCoefficient
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p : FormalMultilinearSeries ℝ Domain G) (m n : ℕ) : G :=
  ∑ s ∈ (Finset.univ : Finset (Fin (m + n))).powersetCard m,
    p (m + n) (polarSlotInput (m + n) s)

lemma polarCoefficient_congr
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {p q : FormalMultilinearSeries ℝ Domain G} {m n : ℕ}
    (h : p (m + n) = q (m + n)) :
    polarCoefficient p m n = polarCoefficient q m n := by
  unfold polarCoefficient
  rw [h]

/-- The ordinary `(m,n)` coefficient of the reduced formal right-hand side. -/
noncomputable def reducedRHSPolarCoefficient
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (u : StateSeries) (m n : ℕ) : FirstOrderState :=
  polarCoefficient (reducedRHS N b u) m n

theorem reducedRHSPolarCoefficient_causal
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    {u v : StateSeries} {m n : ℕ} (h : AgreeUpTo (m + n) u v) :
    reducedRHSPolarCoefficient N b u m n =
      reducedRHSPolarCoefficient N b v m n := by
  apply polarCoefficient_congr
  exact reducedRHS_coeff_causal N b h

/-- Ordinary bivariate coefficients of the two-component state. -/
abbrev BivariateStateCoeff := ℕ → ℕ → FirstOrderState

/-- Canonical homogeneous FMS associated to ordinary state coefficients. -/
noncomputable def stateBivariateFMS (a : BivariateStateCoeff) : StateSeries :=
  FormalMultilinearSeries.pi fun i =>
    CKAnalyticEvaluation.bivariateFMS (fun m n => a m n i)

/-- Agreement of ordinary coefficient arrays through total degree `k`. -/
def CoeffAgreeUpToTotal (k : ℕ)
    (a c : BivariateStateCoeff) : Prop :=
  ∀ m n, m + n ≤ k → a m n = c m n

lemma stateBivariateFMS_coeff_congr
    {a c : BivariateStateCoeff} {k : ℕ}
    (h : ∀ m n, m + n = k → a m n = c m n) :
    stateBivariateFMS a k = stateBivariateFMS c k := by
  ext z i
  simp only [stateBivariateFMS, FormalMultilinearSeries.pi,
    ContinuousMultilinearMap.pi_apply]
  unfold CKAnalyticEvaluation.bivariateFMS
  rw [sum_apply, sum_apply]
  apply Finset.sum_congr rfl
  intro m hm
  have hmk : m ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
  have hac : a m (k - m) = c m (k - m) := by
    apply h
    exact Nat.add_sub_of_le hmk
  have haci : a m (k - m) i = c m (k - m) i := congrFun hac i
  change
    (a m (k - m) i • CKAnalyticEvaluation.polarMonomial k m) z =
      (c m (k - m) i • CKAnalyticEvaluation.polarMonomial k m) z
  rw [haci]

lemma stateBivariateFMS_agreeUpTo
    {a c : BivariateStateCoeff} {k : ℕ}
    (h : CoeffAgreeUpToTotal k a c) :
    AgreeUpTo k (stateBivariateFMS a) (stateBivariateFMS c) := by
  intro d hd
  apply stateBivariateFMS_coeff_congr
  intro m n hmn
  exact h m n (hmn.le.trans hd)

/-- The `(m,n)` coefficient of the reduced right-hand side, now expressed
directly as a function of an ordinary bivariate coefficient array. -/
noncomputable def reducedArrayRHS
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (a : BivariateStateCoeff) (m n : ℕ) : FirstOrderState :=
  reducedRHSPolarCoefficient N b (stateBivariateFMS a) m n

theorem reducedArrayRHS_causal
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    {a c : BivariateStateCoeff} {m n : ℕ}
    (h : CoeffAgreeUpToTotal (m + n) a c) :
    reducedArrayRHS N b a m n = reducedArrayRHS N b c m n := by
  apply reducedRHSPolarCoefficient_causal
  exact stateBivariateFMS_agreeUpTo h

/-- The coefficient obtained by one formal integration in `x`.  Crucially,
the divisor is the new `x` degree `m+1`, not the total degree. -/
noncomputable def reducedNextXCoefficient
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (a : BivariateStateCoeff) (m n : ℕ) : FirstOrderState :=
  ((m + 1 : ℕ) : ℝ)⁻¹ • reducedArrayRHS N b a m n

theorem reducedNextXCoefficient_causal
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    {a c : BivariateStateCoeff} {m n : ℕ}
    (h : CoeffAgreeUpToTotal (m + n) a c) :
    reducedNextXCoefficient N b a m n =
      reducedNextXCoefficient N b c m n := by
  unfold reducedNextXCoefficient
  rw [reducedArrayRHS_causal N b h]

/-- The ordinary coefficient recurrence for `U_x = reducedRHS`. -/
def SatisfiesReducedArrayRecurrence
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (a : BivariateStateCoeff) : Prop :=
  ∀ m n, a (m + 1) n = reducedNextXCoefficient N b a m n

/-- The prescribed analytic Cauchy row on `x=0`. -/
def HasReducedCauchyRow
    (a : BivariateStateCoeff) (cauchy : ℕ → FirstOrderState) : Prop :=
  ∀ n, a 0 n = cauchy n

/-- Strong recursion on total degree constructs the unique formal bivariate
coefficient array. Future coefficients are provisionally filled by zero;
causality proves that this fill is immaterial. -/
noncomputable def formalReducedSolution
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (cauchy : ℕ → FirstOrderState) : BivariateStateCoeff
  | 0, n => cauchy n
  | m + 1, n =>
      reducedNextXCoefficient N b
        (fun i j =>
          if _hij : i + j < (m + 1) + n then
            formalReducedSolution N b cauchy i j
          else 0)
        m n
termination_by m n => m + n
decreasing_by omega

@[simp] theorem formalReducedSolution_zero
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (cauchy : ℕ → FirstOrderState) (n : ℕ) :
    formalReducedSolution N b cauchy 0 n = cauchy n := by
  rw [formalReducedSolution]

theorem formalReducedSolution_succ
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (cauchy : ℕ → FirstOrderState) (m n : ℕ) :
    formalReducedSolution N b cauchy (m + 1) n =
      reducedNextXCoefficient N b (formalReducedSolution N b cauchy) m n := by
  rw [formalReducedSolution]
  apply reducedNextXCoefficient_causal
  intro i j hij
  simp only
  rw [dif_pos]
  omega

theorem formalReducedSolution_hasCauchyRow
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (cauchy : ℕ → FirstOrderState) :
    HasReducedCauchyRow (formalReducedSolution N b cauchy) cauchy := by
  intro n
  exact formalReducedSolution_zero N b cauchy n

theorem formalReducedSolution_satisfiesRecurrence
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (cauchy : ℕ → FirstOrderState) :
    SatisfiesReducedArrayRecurrence N b
      (formalReducedSolution N b cauchy) := by
  intro m n
  exact formalReducedSolution_succ N b cauchy m n

/-- An ordinary formal solution consists of the prescribed `x=0` row and
the exact coefficient recurrence. -/
def IsFormalReducedSolution
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (cauchy : ℕ → FirstOrderState) (a : BivariateStateCoeff) : Prop :=
  HasReducedCauchyRow a cauchy ∧ SatisfiesReducedArrayRecurrence N b a

theorem formalReducedSolution_isFormalSolution
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (cauchy : ℕ → FirstOrderState) :
    IsFormalReducedSolution N b cauchy
      (formalReducedSolution N b cauchy) :=
  ⟨formalReducedSolution_hasCauchyRow N b cauchy,
    formalReducedSolution_satisfiesRecurrence N b cauchy⟩

/-- Total-degree induction gives formal uniqueness for the reduced system. -/
theorem eq_of_cauchyRow_of_recurrence
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (cauchy : ℕ → FirstOrderState) {a c : BivariateStateCoeff}
    (ha0 : HasReducedCauchyRow a cauchy)
    (hc0 : HasReducedCauchyRow c cauchy)
    (ha : SatisfiesReducedArrayRecurrence N b a)
    (hc : SatisfiesReducedArrayRecurrence N b c) : a = c := by
  funext m n
  have H : ∀ d i j, i + j = d → a i j = c i j := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro i j hij
        cases i with
        | zero => exact (ha0 j).trans (hc0 j).symm
        | succ i =>
            rw [ha i j, hc i j]
            apply reducedNextXCoefficient_causal
            intro r s hrs
            apply ih (r + s)
            · omega
            · rfl
  exact H (m + n) m n rfl

theorem IsFormalReducedSolution.unique
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (cauchy : ℕ → FirstOrderState) {a c : BivariateStateCoeff}
    (ha : IsFormalReducedSolution N b cauchy a)
    (hc : IsFormalReducedSolution N b cauchy c) : a = c :=
  eq_of_cauchyRow_of_recurrence N b cauchy ha.1 hc.1 ha.2 hc.2

/-- Every formal analytic coefficient pair `N,b` and Cauchy row determine a
unique ordinary bivariate formal solution. -/
theorem existsUnique_formalReducedSolution
    (N : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderOperator)
    (b : FormalMultilinearSeries ℝ FirstOrderPhase FirstOrderState)
    (cauchy : ℕ → FirstOrderState) :
    ∃! a, IsFormalReducedSolution N b cauchy a := by
  refine ⟨formalReducedSolution N b cauchy,
    formalReducedSolution_isFormalSolution N b cauchy, ?_⟩
  intro a ha
  exact IsFormalReducedSolution.unique N b cauchy ha
    (formalReducedSolution_isFormalSolution N b cauchy)

/-! ## Specialization to the stress-tensor reduced coefficients -/

/-- A fixed quantitative Taylor germ of the reduced principal matrix at the
origin. The choice remains entirely local to Lean's noncomputable logic. -/
noncomputable def firstOrderPrincipalOriginMajorant (P : Params) :
    LocalAnalyticMajorant (firstOrderPrincipalArray P) firstOrderOrigin :=
  Classical.choice (exists_firstOrderPrincipalArray_origin_localAnalyticMajorant P)

/-- A fixed quantitative Taylor germ of the reduced source at the origin. -/
noncomputable def firstOrderSourceOriginMajorant (P : Params) :
    LocalAnalyticMajorant (firstOrderSourceVector P) firstOrderOrigin :=
  Classical.choice (exists_firstOrderSourceVector_origin_localAnalyticMajorant P)

/-- The formal state coefficients selected by the actual analytic principal
matrix and source, with the zero Cauchy row from the reduction. -/
noncomputable def firstOrderFormalCoefficients (P : Params) :
    BivariateStateCoeff :=
  formalReducedSolution
    (firstOrderPrincipalOriginMajorant P).series
    (firstOrderSourceOriginMajorant P).series
    0

@[simp] theorem firstOrderFormalCoefficients_zero_x
    (P : Params) (n : ℕ) :
    firstOrderFormalCoefficients P 0 n = 0 := by
  exact formalReducedSolution_zero _ _ _ n

theorem firstOrderFormalCoefficients_satisfiesRecurrence (P : Params) :
    SatisfiesReducedArrayRecurrence
      (firstOrderPrincipalOriginMajorant P).series
      (firstOrderSourceOriginMajorant P).series
      (firstOrderFormalCoefficients P) :=
  formalReducedSolution_satisfiesRecurrence _ _ _

theorem firstOrderFormalCoefficients_unique (P : Params) :
    ∃! a,
      IsFormalReducedSolution
        (firstOrderPrincipalOriginMajorant P).series
        (firstOrderSourceOriginMajorant P).series 0 a :=
  existsUnique_formalReducedSolution _ _ _

end
end CKFirstOrderFormalSystem
end StressTensor
