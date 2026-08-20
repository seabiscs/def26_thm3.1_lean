import Mathlib.Tactic

/-!
# Formal Cauchy--Kowalevskaya row recursion

This file isolates the algebraic, coefficient-level part of the
Cauchy--Kowalevskaya argument for a second-order equation in normal form

`u_xx = G(x, y, u, u_x, u_y, u_xy, u_yy)`.

A `FormalJet α` is indexed first by the number of `x` derivatives and then by
the number of `y` derivatives.  Thus its row `m` represents
`(∂x^m ∂y^n u)(0, 0)` as `n` varies.  If the coefficient row of the right-hand
side after `m` `x` derivatives depends only on rows through `m + 1`, the normal
form equation determines row `m + 2`.  We record that triangularity explicitly
in `TriangularRHS` and prove existence and uniqueness of the resulting formal
jet.

This is deliberately only a formal recursion theorem.  It makes no assertion
that the resulting coefficients converge, nor that an analytic function with
this jet exists.
-/

namespace StressTensor

namespace CKFormalRecursion

universe u

/-- One row of a two-variable formal derivative jet. -/
abbrev Row (α : Type u) := ℕ → α

/-- A two-variable formal derivative jet, indexed by `x` order and then `y` order. -/
abbrev FormalJet (α : Type u) := ℕ → Row α

/-- Two jets agree in every `x` row up to and including `k`. -/
def AgreeThroughX {α : Type u} (u v : FormalJet α) (k : ℕ) : Prop :=
  ∀ i, i ≤ k → u i = v i

theorem agreeThroughX_refl {α : Type u} (u : FormalJet α) (k : ℕ) :
    AgreeThroughX u u k := by
  intro i hi
  rfl

theorem AgreeThroughX.mono {α : Type u} {u v : FormalJet α} {k l : ℕ}
    (h : AgreeThroughX u v k) (hlk : l ≤ k) : AgreeThroughX u v l := by
  intro i hil
  exact h i (hil.trans hlk)

/--
The five solution-dependent rows visible to a normal-form right-hand side at a
fixed `x`-derivative order.  Shifting the second index represents a `y`
derivative, while `dx` and `dxy` also shift the first index.
-/
@[ext] structure NormalFormRowData (α : Type u) where
  val : Row α
  dx : Row α
  dy : Row α
  dxy : Row α
  dyy : Row α

/-- Extract the formal rows corresponding to `(u, u_x, u_y, u_xy, u_yy)`. -/
def normalFormRowData {α : Type u} (u : FormalJet α) (m : ℕ) :
    NormalFormRowData α where
  val n := u m n
  dx n := u (m + 1) n
  dy n := u m (n + 1)
  dxy n := u (m + 1) (n + 1)
  dyy n := u m (n + 2)

/-- Normal-form row data at order `m` only uses solution rows through `m + 1`. -/
theorem normalFormRowData_eq_of_agreeThroughX {α : Type u}
    {u v : FormalJet α} {m : ℕ} (h : AgreeThroughX u v (m + 1)) :
    normalFormRowData u m = normalFormRowData v m := by
  have hm : u m = v m := h m (by omega)
  have hm1 : u (m + 1) = v (m + 1) := h (m + 1) (by omega)
  ext n <;> simp [normalFormRowData, hm, hm1]

/--
All normal-form argument rows which can enter the coefficient of `x` order
`m`.  This finite `x` history still contains every `y` coefficient in each row.
-/
abbrev NormalFormHistory (α : Type u) (m : ℕ) :=
  (i : Fin (m + 1)) → NormalFormRowData α

/-- Extract the normal-form history through `x` order `m`. -/
def normalFormHistory {α : Type u} (u : FormalJet α) (m : ℕ) :
    NormalFormHistory α m :=
  fun i => normalFormRowData u i

/-- Equal solution rows through `m + 1` give equal normal-form histories through `m`. -/
theorem normalFormHistory_eq_of_agreeThroughX {α : Type u}
    {u v : FormalJet α} {m : ℕ} (h : AgreeThroughX u v (m + 1)) :
    normalFormHistory u m = normalFormHistory v m := by
  funext i
  apply normalFormRowData_eq_of_agreeThroughX
  apply h.mono
  omega

/--
Coefficient data for the right-hand side of a second-order normal-form PDE.

`coeff u m n` is intended to be
`(∂x^m ∂y^n G(x,y,u,u_x,u_y,u_xy,u_yy))(0,0)`.  The `causal` field states the
triangular fact used by CK: this value can inspect `u` only through `x` row
`m + 1`.  In particular, it cannot inspect the as-yet unknown row `m + 2`.
-/
structure TriangularRHS (α : Type u) where
  coeff : FormalJet α → ℕ → Row α
  causal : ∀ {u v : FormalJet α} {m : ℕ},
    AgreeThroughX u v (m + 1) → coeff u m = coeff v m

/--
Build a triangular RHS from any coefficient rule expressed in terms of the
finite normal-form history.  Explicit dependence on `x`, `y`, and fixed
parameters can be carried by the rule itself; the construction tracks only its
dependence on the unknown jet.
-/
def TriangularRHS.ofNormalFormCoefficientRule {α : Type u}
    (rule : (m : ℕ) → NormalFormHistory α m → Row α) : TriangularRHS α where
  coeff u m := rule m (normalFormHistory u m)
  causal := by
    intro u v m h
    rw [normalFormHistory_eq_of_agreeThroughX h]

@[simp] theorem TriangularRHS.ofNormalFormCoefficientRule_coeff {α : Type u}
    (rule : (m : ℕ) → NormalFormHistory α m → Row α)
    (u : FormalJet α) (m : ℕ) :
    (TriangularRHS.ofNormalFormCoefficientRule rule).coeff u m =
      rule m (normalFormHistory u m) := rfl

/-- The formal coefficient recurrence obtained from `u_xx = G(...)`. -/
def SatisfiesRecurrence {α : Type u} (F : TriangularRHS α) (u : FormalJet α) : Prop :=
  ∀ m, u (m + 2) = F.coeff u m

/-- The two rows prescribed by the Cauchy data `u(0,y)` and `u_x(0,y)`. -/
def HasCauchyRows {α : Type u} (u : FormalJet α) (c₀ c₁ : Row α) : Prop :=
  u 0 = c₀ ∧ u 1 = c₁

/-- A formal solution consists exactly of the two Cauchy rows and the CK recurrence. -/
def IsFormalSolution {α : Type u} (F : TriangularRHS α)
    (c₀ c₁ : Row α) (u : FormalJet α) : Prop :=
  HasCauchyRows u c₀ c₁ ∧ SatisfiesRecurrence F u

/--
The row `m + 2` is uniquely determined once all rows through `m + 1` agree.
-/
theorem row_add_two_eq_of_agreeThroughX {α : Type u} (F : TriangularRHS α)
    {u v : FormalJet α} (hu : SatisfiesRecurrence F u)
    (hv : SatisfiesRecurrence F v) {m : ℕ}
    (h : AgreeThroughX u v (m + 1)) :
    u (m + 2) = v (m + 2) := by
  rw [hu m, hv m, F.causal h]

/--
Formal uniqueness: two jets satisfying the same triangular right-hand side and
the same two Cauchy rows agree in every coefficient.
-/
theorem eq_of_cauchyRows_of_recurrence {α : Type u} (F : TriangularRHS α)
    {u v : FormalJet α} (hzero : u 0 = v 0) (hone : u 1 = v 1)
    (hu : SatisfiesRecurrence F u) (hv : SatisfiesRecurrence F v) :
    u = v := by
  funext i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      match i with
      | 0 => exact hzero
      | 1 => exact hone
      | m + 2 =>
          apply row_add_two_eq_of_agreeThroughX F hu hv
          intro j hj
          apply ih j
          omega

/-- A formal solution with fixed Cauchy rows is unique. -/
theorem IsFormalSolution.unique {α : Type u} (F : TriangularRHS α)
    {c₀ c₁ : Row α} {u v : FormalJet α}
    (hu : IsFormalSolution F c₀ c₁ u) (hv : IsFormalSolution F c₀ c₁ v) :
    u = v := by
  exact eq_of_cauchyRows_of_recurrence F
    (hu.1.1.trans hv.1.1.symm) (hu.1.2.trans hv.1.2.symm) hu.2 hv.2

/--
The canonical formal CK jet.  At row `m + 2`, unknown later rows are filled
with the zeroth Cauchy row.  Causality guarantees that this arbitrary filling
does not affect the right-hand-side coefficient being computed.
-/
noncomputable def formalSolution {α : Type u} (F : TriangularRHS α)
    (c₀ c₁ : Row α) : FormalJet α
  | 0 => c₀
  | 1 => c₁
  | m + 2 =>
      F.coeff
        (fun i => if _h : i < m + 2 then formalSolution F c₀ c₁ i else c₀)
        m
termination_by i => i

@[simp] theorem formalSolution_zero {α : Type u} (F : TriangularRHS α)
    (c₀ c₁ : Row α) : formalSolution F c₀ c₁ 0 = c₀ := by
  rw [formalSolution]

@[simp] theorem formalSolution_one {α : Type u} (F : TriangularRHS α)
    (c₀ c₁ : Row α) : formalSolution F c₀ c₁ 1 = c₁ := by
  rw [formalSolution]

/-- The defining row of `formalSolution` is independent of its arbitrary future-row filling. -/
theorem formalSolution_add_two {α : Type u} (F : TriangularRHS α)
    (c₀ c₁ : Row α) (m : ℕ) :
    formalSolution F c₀ c₁ (m + 2) = F.coeff (formalSolution F c₀ c₁) m := by
  rw [formalSolution]
  apply F.causal
  intro i hi
  simp only
  rw [dif_pos]
  omega

/-- The canonical formal jet satisfies every row of the CK recurrence. -/
theorem formalSolution_satisfiesRecurrence {α : Type u} (F : TriangularRHS α)
    (c₀ c₁ : Row α) : SatisfiesRecurrence F (formalSolution F c₀ c₁) := by
  intro m
  exact formalSolution_add_two F c₀ c₁ m

/-- The canonical formal jet has the requested Cauchy rows and solves the recurrence. -/
theorem formalSolution_isFormalSolution {α : Type u} (F : TriangularRHS α)
    (c₀ c₁ : Row α) : IsFormalSolution F c₀ c₁ (formalSolution F c₀ c₁) := by
  exact ⟨⟨formalSolution_zero F c₀ c₁, formalSolution_one F c₀ c₁⟩,
    formalSolution_satisfiesRecurrence F c₀ c₁⟩

/--
Every triangular right-hand side and pair of Cauchy rows have exactly one
formal derivative jet satisfying the second-order recurrence.
-/
theorem existsUnique_isFormalSolution {α : Type u} (F : TriangularRHS α)
    (c₀ c₁ : Row α) : ∃! u, IsFormalSolution F c₀ c₁ u := by
  refine ⟨formalSolution F c₀ c₁, formalSolution_isFormalSolution F c₀ c₁, ?_⟩
  intro u hu
  exact IsFormalSolution.unique F hu (formalSolution_isFormalSolution F c₀ c₁)

end CKFormalRecursion

end StressTensor
