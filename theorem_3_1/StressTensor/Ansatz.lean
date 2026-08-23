import StressTensor.Definitions
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The analytic stress-tensor ansatz

This file formalizes the algebraic and first-order differential identities in
the ansatz part of the construction.  In particular, it records the two
partial derivatives of `u(x,y) = x + y² γ(x,y)`, the exact identity for the
squared gradient, the elementary properties of the continued divided
difference `Ctilde`, and the factorization of the light-cone deficit and of
the scalar prefactor in the stress field.

The stress factorization is stated with explicit positivity hypotheses.  They
are precisely what is needed for the usual multiplication laws for
`Real.rpow`; no convention concerning real powers of negative bases is hidden
in the statement.
-/

namespace StressTensor

noncomputable section

/-! ## The first derivatives of the ansatz -/

/-- The `x` derivative in (3.2). -/
theorem hasDerivAt_ansatz_x
    {γ : ℝ → ℝ → ℝ} {x y γx : ℝ}
    (hγ : HasDerivAt (fun x' => γ x' y) γx x) :
    HasDerivAt (fun x' => ansatz γ x' y) (1 + y ^ 2 * γx) x := by
  have hx : HasDerivAt (fun x' : ℝ => x') 1 x := hasDerivAt_id' x
  have hγ' : HasDerivAt (fun x' => y ^ 2 * γ x' y) (y ^ 2 * γx) x :=
    HasDerivAt.const_mul (y ^ 2) hγ
  change HasDerivAt
    ((fun x' : ℝ => x') + fun x' => y ^ 2 * γ x' y)
    (1 + y ^ 2 * γx) x
  exact HasDerivAt.add hx hγ'

/-- The `y` derivative in (3.2), in the form used to define `Γ₂`. -/
theorem hasDerivAt_ansatz_y
    {γ : ℝ → ℝ → ℝ} {x y γy : ℝ}
    (hγ : HasDerivAt (γ x) γy y) :
    HasDerivAt (fun y' => ansatz γ x y')
      (2 * y * (γ x y + y * γy / 2)) y := by
  have hc : HasDerivAt (fun _y : ℝ => x) 0 y := hasDerivAt_const y x
  have hprod := HasDerivAt.mul (hasDerivAt_pow 2 y) hγ
  have heq :
      0 + ((2 : ℝ) * y ^ (2 - 1) * γ x y + y ^ 2 * γy) =
        2 * y * (γ x y + y * γy / 2) := by
    ring
  change HasDerivAt
    ((fun _y : ℝ => x) + (fun y' : ℝ => y' ^ 2) * γ x)
    (2 * y * (γ x y + y * γy / 2)) y
  rw [← heq]
  exact HasDerivAt.add hc hprod

/-- The `x` derivative agrees with the first component of `ansatzGradient`
when the jet records the value of `∂ₓγ`. -/
theorem hasDerivAt_ansatz_x_eq_gamma1
    {γ : ℝ → ℝ → ℝ} {x y γx : ℝ} (z : Jet)
    (hγ : HasDerivAt (fun x' => γ x' y) γx x) (hz : z.dx = γx) :
    HasDerivAt (fun x' => ansatz γ x' y) (gamma1 y z) x := by
  simpa [gamma1, hz] using hasDerivAt_ansatz_x hγ

/-- The `y` derivative agrees with the second component of `ansatzGradient`
when the jet records `γ` and `∂ᵧγ` at the point. -/
theorem hasDerivAt_ansatz_y_eq_gamma2
    {γ : ℝ → ℝ → ℝ} {x y γy : ℝ} (z : Jet)
    (hγ : HasDerivAt (γ x) γy y)
    (hval : z.val = γ x y) (hdy : z.dy = γy) :
    HasDerivAt (fun y' => ansatz γ x y') (2 * y * gamma2 y z) y := by
  simpa [gamma2, hval, hdy] using hasDerivAt_ansatz_y hγ

/-! ## Squared norm and light-cone deficit -/

/-- Equations (3.3)--(3.5): the squared norm of the predicted gradient is
exactly `1 + y² Γ₀`. -/
theorem normSq_ansatz (y : ℝ) (z : Jet) :
    normSq (ansatzGradient y z) = 1 + y ^ 2 * gamma0 y z := by
  simp only [normSq, ansatzGradient, gamma0, gamma1]
  ring

/-- The gradient lies on the light cone along `y = 0`. -/
@[simp] theorem normSq_ansatz_zero (z : Jet) :
    normSq (ansatzGradient 0 z) = 1 := by
  rw [normSq_ansatz]
  norm_num

/-- The norm identity after applying the real power occurring in the energy. -/
theorem normSq_ansatz_rpow (P : Params) (y : ℝ) (z : Jet) :
    Real.rpow (normSq (ansatzGradient y z)) (P.q / 2) =
      Real.rpow (1 + y ^ 2 * gamma0 y z) (P.q / 2) := by
  rw [normSq_ansatz]

/-! ## The continued divided difference -/

/-- The prescribed value of `Ctilde` on its removable singular set. -/
@[simp] theorem Ctilde_zero (P : Params) (d : ℝ) :
    Ctilde P 0 d = -(P.q * d) / 2 := by
  simp [Ctilde]

/-- The quotient formula for `Ctilde` away from its removable singular set. -/
theorem Ctilde_of_ne_zero (P : Params) {t d : ℝ} (ht : t ≠ 0) :
    Ctilde P t d =
      (1 - Real.rpow (1 + t ^ 2 * d) (P.q / 2)) / t ^ 2 := by
  simp [Ctilde, ht]

/-- The continuation takes the positive value `q` at `(0,-2)`. -/
@[simp] theorem Ctilde_zero_neg_two (P : Params) : Ctilde P 0 (-2) = P.q := by
  simp [Ctilde]

/-- In particular, the center value of `Ctilde` is strictly positive. -/
theorem Ctilde_zero_neg_two_pos (P : Params) : 0 < Ctilde P 0 (-2) := by
  simpa using P.q_pos

/-- `Ctilde` is even in its first variable. -/
theorem Ctilde_neg (P : Params) (t d : ℝ) :
    Ctilde P (-t) d = Ctilde P t d := by
  simp [Ctilde]

/-- The exact divided-difference identity, including `t = 0`. -/
theorem Ctilde_factorization (P : Params) (t d : ℝ) :
    1 - Real.rpow (1 + t ^ 2 * d) (P.q / 2) =
      t ^ 2 * Ctilde P t d := by
  by_cases ht : t = 0
  · subst t
    simp [Ctilde]
  · rw [Ctilde_of_ne_zero P ht]
    field_simp

/-- Equation (3.6): the light-cone deficit factors by `y²` exactly. -/
theorem deficit_factorization (P : Params) (y : ℝ) (z : Jet) :
    1 - Real.rpow (normSq (ansatzGradient y z)) (P.q / 2) =
      y ^ 2 * Ccomp P y z := by
  rw [normSq_ansatz]
  exact Ctilde_factorization P y (gamma0 y z)

/-- The composed continued deficit on the light line. -/
@[simp] theorem Ccomp_zero (P : Params) (z : Jet) :
    Ccomp P 0 z = -(P.q * gamma0 0 z) / 2 := by
  simp [Ccomp]

/-- The composition `C(x,y)` is even under simultaneous replacement of a
jet by one with the same `Γ₀`; this is the algebraic core of its parity. -/
theorem Ccomp_eq_of_gamma0_eq (P : Params) {y y' : ℝ} {z z' : Jet}
    (h : gamma0 y z = gamma0 y' z') (hy : y' = -y) :
    Ccomp P y' z' = Ccomp P y z := by
  subst y'
  simp only [Ccomp]
  rw [← h]
  exact Ctilde_neg P y (gamma0 y z)

/-! ## Real-power bookkeeping and the stress prefactor -/

/-- A square raised to a real power can be written as a power of the absolute
value.  This lemma makes the appearance of `|y|^(2/p)` explicit. -/
theorem rpow_sq (y a : ℝ) :
    Real.rpow (y ^ 2) a = Real.rpow |y| (2 * a) := by
  calc
    Real.rpow (y ^ 2) a = Real.rpow (|y| ^ 2) a := by rw [sq_abs]
    _ = Real.rpow (Real.rpow |y| (2 : ℝ)) a :=
      congrArg (fun b => Real.rpow b a) (Real.rpow_two |y|).symm
    _ = Real.rpow |y| ((2 : ℝ) * a) :=
      (Real.rpow_mul (abs_nonneg y) 2 a).symm

/-- The Hölder relation in the form used for the deficit exponent. -/
theorem Params.one_sub_inv_q (P : Params) : 1 - 1 / P.q = 1 / P.p := by
  linarith [P.holder]

/-- The real power of the factorized deficit.  Positivity of `Ctilde` is kept
explicit, while the square factor only needs nonnegativity. -/
theorem deficit_rpow_factorization
    (P : Params) (t d : ℝ) (hC : 0 ≤ Ctilde P t d) :
    Real.rpow (1 - Real.rpow (1 + t ^ 2 * d) (P.q / 2))
        (1 - 1 / P.q) =
      Real.rpow |t| (2 / P.p) *
        Real.rpow (Ctilde P t d) (1 / P.p) := by
  rw [Ctilde_factorization, P.one_sub_inv_q]
  calc
    Real.rpow (t ^ 2 * Ctilde P t d) (1 / P.p) =
        Real.rpow (t ^ 2) (1 / P.p) *
          Real.rpow (Ctilde P t d) (1 / P.p) :=
      Real.mul_rpow (z := 1 / P.p) (sq_nonneg t) hC
    _ = Real.rpow |t| (2 / P.p) *
          Real.rpow (Ctilde P t d) (1 / P.p) := by
      rw [rpow_sq]
      congr 2
      ring

/-- `Stilde` is even in its first variable. -/
theorem Stilde_neg (P : Params) (t d : ℝ) :
    Stilde P (-t) d = Stilde P t d := by
  simp [Stilde, Ctilde_neg]

/-- The value of `Stilde` on `t = 0`, written as the negative power appearing
in the paper. -/
theorem Stilde_zero (P : Params) (d : ℝ)
    (hC : 0 < -(P.q * d) / 2) :
    Stilde P 0 d =
      Real.rpow (-(P.q * d) / 2) (-1 / P.p) := by
  calc
    Stilde P 0 d =
        1 / Real.rpow (-(P.q * d) / 2) (1 / P.p) := by
      simp [Stilde, Ctilde]
    _ = (Real.rpow (-(P.q * d) / 2) (1 / P.p))⁻¹ := one_div _
    _ = Real.rpow (-(P.q * d) / 2) (-(1 / P.p)) :=
      (Real.rpow_neg hC.le (1 / P.p)).symm
    _ = Real.rpow (-(P.q * d) / 2) (-1 / P.p) := by
      congr 1
      ring

/-- At the distinguished center `(0,-2)`, `Stilde` is `q⁻¹ᐟᵖ`. -/
theorem Stilde_zero_neg_two (P : Params) :
    Stilde P 0 (-2) = Real.rpow P.q (-1 / P.p) := by
  have hq : 0 < -(P.q * (-2)) / 2 := by
    simpa using P.q_pos
  simpa using Stilde_zero P (-2) hq

/-- Scalar form of the stress-field factorization (3.9).  The hypotheses say
that the base of the numerator and the continued deficit factor are positive,
and that one is away from the light line. -/
theorem stressScalar_factorization
    (P : Params) (t d g : ℝ)
    (ht : t ≠ 0) (hbase : 0 < 1 + t ^ 2 * d)
    (hC : 0 < Ctilde P t d) :
    (Real.rpow (1 + t ^ 2 * d) ((P.q - 2) / 2) /
        Real.rpow (1 - Real.rpow (1 + t ^ 2 * d) (P.q / 2))
          (1 - 1 / P.q)) * g =
      (Stilde P t d / Real.rpow |t| (2 / P.p)) * g := by
  have _hbaseRpow :
      0 < Real.rpow (1 + t ^ 2 * d) ((P.q - 2) / 2) :=
    Real.rpow_pos_of_pos hbase _
  have habs : 0 < |t| := abs_pos.mpr ht
  have habsrpow : Real.rpow |t| (2 / P.p) ≠ 0 :=
    (Real.rpow_pos_of_pos habs _).ne'
  have hCrpow : Real.rpow (Ctilde P t d) (1 / P.p) ≠ 0 :=
    (Real.rpow_pos_of_pos hC _).ne'
  rw [deficit_rpow_factorization P t d hC.le, Stilde]
  field_simp

/-- Vector form of the same factorization for the ansatz gradient. -/
theorem stressVector_factorization
    (P : Params) (y : ℝ) (z : Jet)
    (hy : y ≠ 0) (hbase : 0 < 1 + y ^ 2 * gamma0 y z)
    (hC : 0 < Ccomp P y z) :
    (Real.rpow (normSq (ansatzGradient y z)) ((P.q - 2) / 2) /
        Real.rpow
          (1 - Real.rpow (normSq (ansatzGradient y z)) (P.q / 2))
          (1 - 1 / P.q)) • ansatzGradient y z =
      (Scomp P y z / Real.rpow |y| (2 / P.p)) • ansatzGradient y z := by
  rw [normSq_ansatz]
  have hscalar := stressScalar_factorization P y (gamma0 y z) 1 hy hbase hC
  simp only [mul_one] at hscalar
  rw [hscalar]
  rfl

end

end StressTensor
