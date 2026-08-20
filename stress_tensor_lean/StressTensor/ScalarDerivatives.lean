import StressTensor.Ansatz
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar derivatives in the stress-tensor ansatz

This file proves the derivative with respect to the second variable of
`Ctilde`, including the removable singular set `t = 0`, and derives the
logarithmic derivative of `Stilde` used in (3.20).  All real-power rules are
applied under explicit positivity hypotheses.
-/

namespace StressTensor

noncomputable section

/-! ## The `d` derivative of `Ctilde` -/

/-- The affine base `d ↦ 1 + t²d` has derivative `t²`. -/
private theorem hasDerivAt_affineBase (t d : ℝ) :
    HasDerivAt (fun d' : ℝ => 1 + t ^ 2 * d') (t ^ 2) d := by
  have hmul : HasDerivAt (fun d' : ℝ => t ^ 2 * d') (t ^ 2) d :=
    (HasDerivAt.const_mul (t ^ 2) (hasDerivAt_id' d)).congr_deriv (by ring)
  exact hmul.const_add 1

/-- The `d` derivative of `Ctilde` at `t = 0`. -/
theorem hasDerivAt_Ctilde_d_zero (P : Params) (d : ℝ) :
    HasDerivAt (fun d' => Ctilde P 0 d') (-(P.q / 2)) d := by
  have hmul : HasDerivAt (fun d' : ℝ => P.q * d') P.q d :=
    (HasDerivAt.const_mul P.q (hasDerivAt_id' d)).congr_deriv (by ring)
  have hquot := HasDerivAt.div_const (HasDerivAt.neg hmul) (2 : ℝ)
  have hcoeff : -P.q / 2 = -(P.q / 2) := by ring
  apply (hquot.congr_deriv hcoeff).congr_of_eventuallyEq
  filter_upwards with d'
  simp [Ctilde]

/-- Formula (3.20) for `∂d Ctilde` away from `t = 0`. -/
theorem hasDerivAt_Ctilde_d_of_ne_zero
    (P : Params) {t d : ℝ} (ht : t ≠ 0)
    (hbase : 0 < 1 + t ^ 2 * d) :
    HasDerivAt (fun d' => Ctilde P t d')
      (-(P.q / 2) *
        Real.rpow (1 + t ^ 2 * d) (-1 + P.q / 2)) d := by
  let base : ℝ → ℝ := fun d' => 1 + t ^ 2 * d'
  have hbaseDeriv : HasDerivAt base (t ^ 2) d := by
    simpa only [base] using hasDerivAt_affineBase t d
  have hpow :
      HasDerivAt (fun d' => Real.rpow (base d') (P.q / 2))
        (t ^ 2 * (P.q / 2) *
          Real.rpow (base d) (P.q / 2 - 1)) d :=
    HasDerivAt.rpow_const hbaseDeriv (Or.inl hbase.ne')
  have hnum := HasDerivAt.const_sub 1 hpow
  have hquot := HasDerivAt.div_const hnum (t ^ 2)
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
  have hexp : P.q / 2 - 1 = -1 + P.q / 2 := by ring
  have hcoeff :
      (-(t ^ 2 * (P.q / 2) *
          Real.rpow (base d) (P.q / 2 - 1))) / t ^ 2 =
        -(P.q / 2) *
          Real.rpow (1 + t ^ 2 * d) (-1 + P.q / 2) := by
    simp only [base, hexp]
    field_simp
  simpa only [Ctilde, ht, if_false, base] using
    hquot.congr_deriv hcoeff

/-- Formula (3.20), valid also on the removable singular set. -/
theorem hasDerivAt_Ctilde_d
    (P : Params) (t d : ℝ) (hbase : 0 < 1 + t ^ 2 * d) :
    HasDerivAt (fun d' => Ctilde P t d')
      (-(P.q / 2) *
        Real.rpow (1 + t ^ 2 * d) (-1 + P.q / 2)) d := by
  by_cases ht : t = 0
  · subst t
    simpa using hasDerivAt_Ctilde_d_zero P d
  · exact hasDerivAt_Ctilde_d_of_ne_zero P ht hbase

/-- The corresponding formula stated using `deriv`. -/
theorem deriv_Ctilde_d
    (P : Params) (t d : ℝ) (hbase : 0 < 1 + t ^ 2 * d) :
    deriv (fun d' => Ctilde P t d') d =
      -(P.q / 2) *
        Real.rpow (1 + t ^ 2 * d) (-1 + P.q / 2) :=
  (hasDerivAt_Ctilde_d P t d hbase).deriv

/-! ## Logarithmic derivatives and `Stilde` -/

/-- Repackage the derivative of a positive real power as the value of the
power times its logarithmic derivative. -/
private theorem HasDerivAt.rpow_const_mul_logDerivative
    {f : ℝ → ℝ} {f' x a : ℝ} (hf : HasDerivAt f f' x)
    (hfx : 0 < f x) :
    HasDerivAt (fun y => Real.rpow (f y) a)
      (Real.rpow (f x) a * (a * f' / f x)) x := by
  have hraw := HasDerivAt.rpow_const (p := a) hf (Or.inl hfx.ne')
  apply hraw.congr_deriv
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_sub hfx a 1, Real.rpow_one]
  field_simp

/-- A quotient rule expressed in logarithmic-derivative form. -/
private theorem HasDerivAt.div_mul_logDerivative
    {f g : ℝ → ℝ} {α β x : ℝ}
    (hf : HasDerivAt f (f x * α) x)
    (hg : HasDerivAt g (g x * β) x) (hg0 : g x ≠ 0) :
    HasDerivAt (fun y => f y / g y)
      ((f x / g x) * (α - β)) x := by
  have hquot := HasDerivAt.fun_div hf hg hg0
  apply hquot.congr_deriv
  field_simp

/-- The right-hand side of the logarithmic derivative identity (3.20). -/
noncomputable def stildeDLogRate (P : Params) (t d : ℝ) : ℝ :=
  ((P.q - 2) / 2) * t ^ 2 / (1 + t ^ 2 * d) +
    P.q * Real.rpow (1 + t ^ 2 * d) (-1 + P.q / 2) /
      (2 * P.p * Ctilde P t d)

/-- Positivity of `Stilde` on the natural positive-base region. -/
theorem Stilde_pos_of_pos
    (P : Params) (t d : ℝ) (hbase : 0 < 1 + t ^ 2 * d)
    (hC : 0 < Ctilde P t d) : 0 < Stilde P t d := by
  exact div_pos (Real.rpow_pos_of_pos hbase _)
    (Real.rpow_pos_of_pos hC _)

/-- The `d` derivative of `Stilde`: its derivative is its value times the
right-hand side in (3.20). -/
theorem hasDerivAt_Stilde_d
    (P : Params) (t d : ℝ) (hbase : 0 < 1 + t ^ 2 * d)
    (hC : 0 < Ctilde P t d) :
    HasDerivAt (fun d' => Stilde P t d')
      (Stilde P t d * stildeDLogRate P t d) d := by
  let base : ℝ → ℝ := fun d' => 1 + t ^ 2 * d'
  let cfun : ℝ → ℝ := fun d' => Ctilde P t d'
  let a : ℝ := (P.q - 2) / 2
  let b : ℝ := 1 / P.p
  let c' : ℝ := -(P.q / 2) *
    Real.rpow (1 + t ^ 2 * d) (-1 + P.q / 2)
  have hbaseDeriv : HasDerivAt base (t ^ 2) d := by
    simpa only [base] using hasDerivAt_affineBase t d
  have hcDeriv : HasDerivAt cfun c' d := by
    simpa only [cfun, c'] using hasDerivAt_Ctilde_d P t d hbase
  have hA := HasDerivAt.rpow_const_mul_logDerivative
    hbaseDeriv hbase (a := a)
  have hD := HasDerivAt.rpow_const_mul_logDerivative
    hcDeriv hC (a := b)
  have hD0 : Real.rpow (cfun d) b ≠ 0 :=
    (Real.rpow_pos_of_pos hC b).ne'
  have hquot := HasDerivAt.div_mul_logDerivative hA hD hD0
  have hrate :
      a * t ^ 2 / base d - b * c' / cfun d =
        stildeDLogRate P t d := by
    simp only [a, b, c', base, cfun, stildeDLogRate]
    field_simp [P.p_pos.ne']
    ring
  have hquot' := hquot.congr_deriv (by rw [hrate])
  simpa only [Stilde, base, cfun, a, b] using hquot'

/-- The same result as an exact derivative identity. -/
theorem deriv_Stilde_d
    (P : Params) (t d : ℝ) (hbase : 0 < 1 + t ^ 2 * d)
    (hC : 0 < Ctilde P t d) :
    deriv (fun d' => Stilde P t d') d =
      Stilde P t d * stildeDLogRate P t d :=
  (hasDerivAt_Stilde_d P t d hbase hC).deriv

/-- Formula (3.20) in its displayed ratio form. -/
theorem deriv_Stilde_d_div
    (P : Params) (t d : ℝ) (hbase : 0 < 1 + t ^ 2 * d)
    (hC : 0 < Ctilde P t d) :
    deriv (fun d' => Stilde P t d') d / Stilde P t d =
      stildeDLogRate P t d := by
  rw [deriv_Stilde_d P t d hbase hC]
  field_simp [(Stilde_pos_of_pos P t d hbase hC).ne']

/-- Equivalently, the derivative of `log Stilde` is the rate in (3.20). -/
theorem hasDerivAt_log_Stilde_d
    (P : Params) (t d : ℝ) (hbase : 0 < 1 + t ^ 2 * d)
    (hC : 0 < Ctilde P t d) :
    HasDerivAt (fun d' => Real.log (Stilde P t d'))
      (stildeDLogRate P t d) d := by
  have hlog := (hasDerivAt_Stilde_d P t d hbase hC).log
    (Stilde_pos_of_pos P t d hbase hC).ne'
  apply hlog.congr_deriv
  field_simp [(Stilde_pos_of_pos P t d hbase hC).ne']

/-! ## Even functions at the origin -/

/-- A differentiable even real function has zero derivative at the origin,
stated directly for a supplied `HasDerivAt` witness. -/
theorem derivative_eq_zero_of_even
    {f : ℝ → ℝ} {a : ℝ} (heven : ∀ x, f (-x) = f x)
    (hf : HasDerivAt f a 0) : a = 0 := by
  have hfun : (fun x => f (-x)) = f := funext heven
  have hderiv : deriv f 0 = -deriv f 0 := by
    calc
      deriv f 0 = deriv (fun x => f (-x)) 0 := by rw [hfun]
      _ = -deriv f (-0) := deriv_comp_neg f 0
      _ = -deriv f 0 := by norm_num
  linarith [hf.deriv]

/-- Conditional application of the even-function lemma to `t ↦ Stilde t d`.
The analyticity argument supplying differentiability at the removable
singularity is deliberately kept as an explicit hypothesis. -/
theorem hasDerivAt_Stilde_t_zero_of_differentiableAt
    (P : Params) (d : ℝ)
    (hS : DifferentiableAt ℝ (fun t => Stilde P t d) 0) :
    HasDerivAt (fun t => Stilde P t d) 0 0 := by
  have hraw := hS.hasDerivAt
  apply hraw.congr_deriv
  exact derivative_eq_zero_of_even (Stilde_neg P · d) hraw

end

end StressTensor
