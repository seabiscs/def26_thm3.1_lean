import StressTensor.CKFirstOrderConvergence

/-!
# Diagonal congruence for formal composition and action

Formal multilinear series need not be determined by their diagonal values at
the level of raw multilinear maps.  The constructions used by the reduced
stress system, however, preserve equality of homogeneous diagonal
evaluations.  This file records that interface for formal composition and
for the generic formal matrix action.

The composition result is completely domain-generic.  The action results use
the fixed two-component matrix/vector codomains of the first-order stress
system, but allow an arbitrary real normed input space.
-/

namespace StressTensor
namespace CKFormalDiagonalCongruence

open CKFirstOrderFormalSystem CKFirstOrderConvergence

noncomputable section

/-! ## Diagonal equivalence of formal multilinear series -/

/-- Two formal multilinear series are diagonally equivalent if every
homogeneous coefficient agrees when all inputs are equal. -/
def DiagonallyEquivalent
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p q : FormalMultilinearSeries ℝ E F) : Prop :=
  ∀ k z, p k (fun _ : Fin k => z) = q k (fun _ : Fin k => z)

@[refl] theorem DiagonallyEquivalent.refl
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : FormalMultilinearSeries ℝ E F) :
    DiagonallyEquivalent p p := by
  intro k z
  rfl

@[symm] theorem DiagonallyEquivalent.symm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p q : FormalMultilinearSeries ℝ E F}
    (h : DiagonallyEquivalent p q) :
    DiagonallyEquivalent q p := by
  intro k z
  exact (h k z).symm

@[trans] theorem DiagonallyEquivalent.trans
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p q r : FormalMultilinearSeries ℝ E F}
    (hpq : DiagonallyEquivalent p q)
    (hqr : DiagonallyEquivalent q r) :
    DiagonallyEquivalent p r := by
  intro k z
  exact (hpq k z).trans (hqr k z)

/-! ## Formal composition -/

/-- At a diagonal input, `q.comp p` depends on each inner homogeneous map
only through its diagonal evaluation. -/
theorem comp_apply_diag_congr_inner
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (q : FormalMultilinearSeries ℝ F G)
    {p r : FormalMultilinearSeries ℝ E F}
    (hpr : DiagonallyEquivalent p r)
    (k : ℕ) (z : E) :
    q.comp p k (fun _ : Fin k => z) =
      q.comp r k (fun _ : Fin k => z) := by
  unfold FormalMultilinearSeries.comp
  rw [sum_apply, sum_apply]
  apply Finset.sum_congr rfl
  intro c hc
  simp only [FormalMultilinearSeries.compAlongComposition_apply]
  congr 1
  funext i
  unfold FormalMultilinearSeries.applyComposition
  have hdiag :
      ((fun _ : Fin k => z) ∘ c.embedding i) =
        (fun _ : Fin (c.blocksFun i) => z) := by
    funext j
    rfl
  rw [hdiag]
  exact hpr (c.blocksFun i) z

/-- Formal composition respects diagonal equivalence in its inner series. -/
theorem comp_diagonallyEquivalent_inner
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (q : FormalMultilinearSeries ℝ F G)
    {p r : FormalMultilinearSeries ℝ E F}
    (hpr : DiagonallyEquivalent p r) :
    DiagonallyEquivalent (q.comp p) (q.comp r) := by
  intro k z
  exact comp_apply_diag_congr_inner q hpr k z

/-! ## Generic formal matrix action -/

section GenericActionDomain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- On a diagonal input, one generic homogeneous action summand is the
ordinary matrix action of the two diagonal homogeneous evaluations. -/
theorem actionHomogeneousOn_apply_diag
    (A : FormalMultilinearSeries ℝ E FirstOrderOperator)
    (u : FormalMultilinearSeries ℝ E FirstOrderState)
    (k i : ℕ) (z : E) (hi : i ≤ k) :
    actionHomogeneousOn A u k i (fun _ : Fin k => z) =
      operatorActionCLM
        (A i (fun _ : Fin i => z))
        (u (k - i) (fun _ : Fin (k - i) => z)) := by
  simp only [actionHomogeneousOn, dif_pos hi,
    ContinuousMultilinearMap.domDomCongr_apply, splitActionFinOn_apply]
  congr 2

/-- Diagonal evaluation of the generic formal action is its finite Cauchy
convolution. -/
theorem formalActionOn_apply_diag
    (A : FormalMultilinearSeries ℝ E FirstOrderOperator)
    (u : FormalMultilinearSeries ℝ E FirstOrderState)
    (k : ℕ) (z : E) :
    formalActionOn A u k (fun _ : Fin k => z) =
      ∑ i ∈ Finset.range (k + 1),
        operatorActionCLM
          (A i (fun _ : Fin i => z))
          (u (k - i) (fun _ : Fin (k - i) => z)) := by
  rw [formalActionOn, sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact actionHomogeneousOn_apply_diag A u k i z
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

/-- Degree-local congruence for generic formal action at one diagonal input.
Only degrees at most `k` are needed. -/
theorem formalActionOn_apply_diag_congr_of_forall_le
    {A B : FormalMultilinearSeries ℝ E FirstOrderOperator}
    {u v : FormalMultilinearSeries ℝ E FirstOrderState}
    {k : ℕ} {z : E}
    (hA : ∀ i, i ≤ k →
      A i (fun _ : Fin i => z) = B i (fun _ : Fin i => z))
    (hu : ∀ j, j ≤ k →
      u j (fun _ : Fin j => z) = v j (fun _ : Fin j => z)) :
    formalActionOn A u k (fun _ : Fin k => z) =
      formalActionOn B v k (fun _ : Fin k => z) := by
  rw [formalActionOn_apply_diag, formalActionOn_apply_diag]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [hA i hik, hu (k - i) (Nat.sub_le k i)]

/-- Generic formal action respects diagonal equivalence of both its operator
and vector series. -/
theorem formalActionOn_diagonallyEquivalent
    {A B : FormalMultilinearSeries ℝ E FirstOrderOperator}
    {u v : FormalMultilinearSeries ℝ E FirstOrderState}
    (hA : DiagonallyEquivalent A B)
    (hu : DiagonallyEquivalent u v) :
    DiagonallyEquivalent (formalActionOn A u) (formalActionOn B v) := by
  intro k z
  apply formalActionOn_apply_diag_congr_of_forall_le
  · intro i hi
    exact hA i z
  · intro j hj
    exact hu j z

end GenericActionDomain

/-! ## Specialization to the reduced stress-system action -/

/-- The original two-variable `formalAction` is definitionally the generic
construction specialized to `Domain`. -/
theorem formalAction_eq_formalActionOn
    (A : OperatorSeries) (u : StateSeries) :
    formalAction A u = formalActionOn A u := by
  rfl

/-- Diagonal Cauchy-product formula for the original reduced-system formal
action, obtained from the generic construction. -/
theorem formalAction_apply_diag
    (A : OperatorSeries) (u : StateSeries) (k : ℕ) (z : Domain) :
    formalAction A u k (fun _ : Fin k => z) =
      ∑ i ∈ Finset.range (k + 1),
        operatorActionCLM
          (A i (fun _ : Fin i => z))
          (u (k - i) (fun _ : Fin (k - i) => z)) := by
  change
    formalActionOn A u k (fun _ : Fin k => z) =
      ∑ i ∈ Finset.range (k + 1),
        operatorActionCLM
          (A i (fun _ : Fin i => z))
          (u (k - i) (fun _ : Fin (k - i) => z))
  exact formalActionOn_apply_diag A u k z

end

end CKFormalDiagonalCongruence
end StressTensor
