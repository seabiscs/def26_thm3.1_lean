import StressTensor.CKFirstOrderFormalSystem
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Evaluation of formal operator actions

This file supplies the analytic bridge between the diagonal Cauchy product
used by `CKFirstOrderFormalSystem.formalAction` and ordinary pointwise action
of a convergent operator-valued series on a convergent vector-valued series.

The first section is independent of the stress-tensor system: a curried
continuous bilinear map sends two summable series to their Cauchy product,
provided the associated double family is summable.  The second section
identifies that generic Cauchy product with the custom homogeneous
`formalAction` construction.
-/

namespace StressTensor
namespace CKFormalActionEvaluation

noncomputable section

section ContinuousBilinearCauchyProduct

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

variable {I J : Type*}

/-- A curried continuous bilinear map commutes with two infinite sums once
the resulting double family is known to be summable. -/
theorem HasSum.continuousLinearMap_apply_eq
    (B : E →L[ℝ] F →L[ℝ] G)
    {f : I → E} {g : J → F} {s : E} {t : F} {u : G}
    (hf : HasSum f s) (hg : HasSum g t)
    (hfg : HasSum (fun ij : I × J => B (f ij.1) (g ij.2)) u) :
    B s t = u := by
  have houter : HasSum (fun i => B (f i) t) (B s t) :=
    ((ContinuousLinearMap.apply ℝ G t).comp B).hasSum hf
  have hinner : ∀ i : I,
      HasSum (fun j => B (f i) (g j)) (B (f i) t) :=
    fun i => (B (f i)).hasSum hg
  have hcollapse : HasSum (fun i => B (f i) t) u :=
    HasSum.prod_fiberwise hfg hinner
  exact houter.unique hcollapse

/-- Has-sum form of the double-series identity for a curried continuous
bilinear map. -/
theorem HasSum.continuousLinearMap_apply
    (B : E →L[ℝ] F →L[ℝ] G)
    {f : I → E} {g : J → F} {s : E} {t : F}
    (hf : HasSum f s) (hg : HasSum g t)
    (hfg : Summable (fun ij : I × J => B (f ij.1) (g ij.2))) :
    HasSum (fun ij : I × J => B (f ij.1) (g ij.2)) (B s t) := by
  let ⟨u, hu⟩ := hfg
  exact
    (HasSum.continuousLinearMap_apply_eq B hf hg hu).symm ▸ hu

/-- Absolute convergence of the two input families implies summability of
the double family obtained by applying a continuous bilinear map. -/
theorem summable_continuousLinearMap_apply_prod_of_summable_norm
    [CompleteSpace G]
    (B : E →L[ℝ] F →L[ℝ] G)
    {f : I → E} {g : J → F}
    (hf : Summable (fun i => ‖f i‖))
    (hg : Summable (fun j => ‖g j‖)) :
    Summable (fun ij : I × J => B (f ij.1) (g ij.2)) := by
  have hscalar : Summable (fun ij : I × J =>
      (‖B‖ * ‖f ij.1‖) * ‖g ij.2‖) := by
    simpa only [mul_assoc] using
      (hf.mul_of_nonneg hg (fun i => norm_nonneg (f i))
        (fun j => norm_nonneg (g j))).mul_left ‖B‖
  apply hscalar.of_norm_bounded
  intro ij
  exact (B (f ij.1)).le_opNorm (g ij.2) |>.trans
    (mul_le_mul_of_nonneg_right (B.le_opNorm (f ij.1)) (norm_nonneg _))

/-- Summability of a double family implies summability after collecting its
terms by total degree. -/
theorem summable_sum_continuousLinearMap_antidiagonal
    (B : E →L[ℝ] F →L[ℝ] G)
    {f : ℕ → E} {g : ℕ → F}
    (hfg : Summable (fun ij : ℕ × ℕ => B (f ij.1) (g ij.2))) :
    Summable (fun n : ℕ =>
      ∑ ij ∈ Finset.antidiagonal n, B (f ij.1) (g ij.2)) := by
  have hsigma : Summable
      (fun x : Σ n : ℕ, Finset.antidiagonal n =>
        B (f (x.2 : ℕ × ℕ).1) (g (x.2 : ℕ × ℕ).2)) :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.symm.mp hfg
  conv =>
    congr
    ext n
    rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
  exact hsigma.sigma' fun n => (hasSum_fintype _).summable

/-- Cauchy-product formula for a curried continuous bilinear map, indexed
with `Finset.antidiagonal`. -/
theorem HasSum.continuousLinearMap_apply_cauchy_antidiagonal
    (B : E →L[ℝ] F →L[ℝ] G)
    {f : ℕ → E} {g : ℕ → F} {s : E} {t : F}
    (hf : HasSum f s) (hg : HasSum g t)
    (hfg : Summable (fun ij : ℕ × ℕ => B (f ij.1) (g ij.2))) :
    HasSum (fun n : ℕ =>
      ∑ ij ∈ Finset.antidiagonal n, B (f ij.1) (g ij.2)) (B s t) := by
  have houter := summable_sum_continuousLinearMap_antidiagonal B hfg
  have hpair := HasSum.continuousLinearMap_apply B hf hg hfg
  have heq : B s t =
      ∑' n : ℕ, ∑ ij ∈ Finset.antidiagonal n,
        B (f ij.1) (g ij.2) := by
    rw [← hpair.tsum_eq,
      ← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq
        (fun ij : ℕ × ℕ => B (f ij.1) (g ij.2))]
    conv_rhs =>
      congr
      ext n
      rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
    exact
      (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.symm.mp hfg).tsum_sigma'
        (fun n => (hasSum_fintype _).summable)
  exact heq.symm ▸ houter.hasSum

/-- Cauchy-product formula for a curried continuous bilinear map, in the
subtraction-based `Finset.range (n + 1)` form used by `formalAction`. -/
theorem HasSum.continuousLinearMap_apply_cauchy_range
    (B : E →L[ℝ] F →L[ℝ] G)
    {f : ℕ → E} {g : ℕ → F} {s : E} {t : F}
    (hf : HasSum f s) (hg : HasSum g t)
    (hfg : Summable (fun ij : ℕ × ℕ => B (f ij.1) (g ij.2))) :
    HasSum (fun n : ℕ =>
      ∑ i ∈ Finset.range (n + 1), B (f i) (g (n - i))) (B s t) := by
  simpa only [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => B (f i) (g j))] using
    HasSum.continuousLinearMap_apply_cauchy_antidiagonal B hf hg hfg

/-- Absolute-convergence version of the continuous-bilinear Cauchy product;
the double-family summability premise is discharged automatically. -/
theorem HasSum.continuousLinearMap_apply_cauchy_range_of_summable_norm
    [CompleteSpace G]
    (B : E →L[ℝ] F →L[ℝ] G)
    {f : ℕ → E} {g : ℕ → F} {s : E} {t : F}
    (hf : HasSum f s) (hg : HasSum g t)
    (hfnorm : Summable (fun n => ‖f n‖))
    (hgnorm : Summable (fun n => ‖g n‖)) :
    HasSum (fun n : ℕ =>
      ∑ i ∈ Finset.range (n + 1), B (f i) (g (n - i))) (B s t) :=
  HasSum.continuousLinearMap_apply_cauchy_range B hf hg
    (summable_continuousLinearMap_apply_prod_of_summable_norm B hfnorm hgnorm)

end ContinuousBilinearCauchyProduct

section FormalAction

open CKFirstOrderFormalSystem

/-- On a diagonal input, one homogeneous summand of `formalAction` is the
ordinary action of the two evaluated homogeneous coefficients. -/
theorem actionHomogeneous_apply_diag
    (A : OperatorSeries) (u : StateSeries) (k i : ℕ)
    (p : Domain) (hi : i ≤ k) :
    actionHomogeneous A u k i (fun _ : Fin k => p) =
      operatorActionCLM
        (A i (fun _ : Fin i => p))
        (u (k - i) (fun _ : Fin (k - i) => p)) := by
  simp only [actionHomogeneous, dif_pos hi,
    ContinuousMultilinearMap.domDomCongr_apply, splitActionFin_apply]
  congr 2

/-- Evaluating a homogeneous coefficient of `formalAction` on a diagonal
input gives precisely the finite Cauchy convolution of the evaluated
operator and state coefficients. -/
theorem formalAction_apply_diag
    (A : OperatorSeries) (u : StateSeries) (k : ℕ) (p : Domain) :
    formalAction A u k (fun _ : Fin k => p) =
      ∑ i ∈ Finset.range (k + 1),
        operatorActionCLM
          (A i (fun _ : Fin i => p))
          (u (k - i) (fun _ : Fin (k - i) => p)) := by
  rw [formalAction, sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact actionHomogeneous_apply_diag A u k i p
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

/-- Matrix-vector form of `formalAction_apply_diag`. -/
theorem formalAction_apply_diag_mulVec
    (A : OperatorSeries) (u : StateSeries) (k : ℕ) (p : Domain) :
    formalAction A u k (fun _ : Fin k => p) =
      ∑ i ∈ Finset.range (k + 1),
        Matrix.mulVec
          (A i (fun _ : Fin i => p))
          (u (k - i) (fun _ : Fin (k - i) => p)) := by
  simpa only [operatorActionCLM_apply] using formalAction_apply_diag A u k p

/-- Coordinate form of the two-component matrix-vector convolution. -/
theorem formalAction_apply_diag_component
    (A : OperatorSeries) (u : StateSeries) (k : ℕ) (p : Domain)
    (a : Fin 2) :
    formalAction A u k (fun _ : Fin k => p) a =
      ∑ i ∈ Finset.range (k + 1), ∑ b : Fin 2,
        A i (fun _ : Fin i => p) a b *
          u (k - i) (fun _ : Fin (k - i) => p) b := by
  rw [formalAction_apply_diag_mulVec, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-- If the evaluated operator and vector series converge and their double
action family is summable, then evaluating `formalAction` sums to the
pointwise operator action of their sums. -/
theorem hasSum_formalAction_apply_diag
    (A : OperatorSeries) (u : StateSeries) (p : Domain)
    {Asum : FirstOrderOperator} {usum : FirstOrderState}
    (hA : HasSum (fun n : ℕ => A n (fun _ : Fin n => p)) Asum)
    (hu : HasSum (fun n : ℕ => u n (fun _ : Fin n => p)) usum)
    (hprod : Summable (fun ij : ℕ × ℕ =>
      operatorActionCLM
        (A ij.1 (fun _ : Fin ij.1 => p))
        (u ij.2 (fun _ : Fin ij.2 => p)))) :
    HasSum (fun k : ℕ => formalAction A u k (fun _ : Fin k => p))
      (operatorActionCLM Asum usum) := by
  simpa only [formalAction_apply_diag] using
    HasSum.continuousLinearMap_apply_cauchy_range operatorActionCLM hA hu hprod

/-- Concrete matrix-vector conclusion of
`hasSum_formalAction_apply_diag`. -/
theorem hasSum_formalAction_apply_diag_mulVec
    (A : OperatorSeries) (u : StateSeries) (p : Domain)
    {Asum : FirstOrderOperator} {usum : FirstOrderState}
    (hA : HasSum (fun n : ℕ => A n (fun _ : Fin n => p)) Asum)
    (hu : HasSum (fun n : ℕ => u n (fun _ : Fin n => p)) usum)
    (hprod : Summable (fun ij : ℕ × ℕ =>
      operatorActionCLM
        (A ij.1 (fun _ : Fin ij.1 => p))
        (u ij.2 (fun _ : Fin ij.2 => p)))) :
    HasSum (fun k : ℕ => formalAction A u k (fun _ : Fin k => p))
      (Matrix.mulVec Asum usum) := by
  simpa only [operatorActionCLM_apply] using
    hasSum_formalAction_apply_diag A u p hA hu hprod

/-- Absolute-convergence version of `hasSum_formalAction_apply_diag`; this
is the form directly discharged by formal-power-series radius estimates. -/
theorem hasSum_formalAction_apply_diag_of_summable_norm
    (A : OperatorSeries) (u : StateSeries) (p : Domain)
    {Asum : FirstOrderOperator} {usum : FirstOrderState}
    (hA : HasSum (fun n : ℕ => A n (fun _ : Fin n => p)) Asum)
    (hu : HasSum (fun n : ℕ => u n (fun _ : Fin n => p)) usum)
    (hAnorm : Summable (fun n : ℕ =>
      ‖A n (fun _ : Fin n => p)‖))
    (hunorm : Summable (fun n : ℕ =>
      ‖u n (fun _ : Fin n => p)‖)) :
    HasSum (fun k : ℕ => formalAction A u k (fun _ : Fin k => p))
      (Matrix.mulVec Asum usum) := by
  have hprod :=
    summable_continuousLinearMap_apply_prod_of_summable_norm
      operatorActionCLM hAnorm hunorm
  exact hasSum_formalAction_apply_diag_mulVec A u p hA hu hprod

end FormalAction

end

end CKFormalActionEvaluation
end StressTensor
