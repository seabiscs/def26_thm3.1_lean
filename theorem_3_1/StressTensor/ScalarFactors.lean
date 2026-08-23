import StressTensor.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integral representation of the scalar deficit factor

This file relates the integral formula for `C̃` in (3.6) to the quotient
formula used by `Ctilde`.  The positivity assumption in the comparison
theorem keeps the affine base of `Real.rpow` in its smooth positive region
along the whole integration segment.
-/

namespace StressTensor

noncomputable section

/-- The integral representation
`-(q d / 2) ∫₀¹ (1 + τ t² d)^((q - 2) / 2) dτ` from (3.6). -/
def CtildeIntegral (P : Params) (t d : ℝ) : ℝ :=
  -(P.q * d / 2) *
    ∫ τ in (0 : ℝ)..1, Real.rpow (1 + τ * t ^ 2 * d) ((P.q - 2) / 2)

/-- At `t = 0`, the integral representation has the prescribed continuation value. -/
@[simp] theorem CtildeIntegral_zero (P : Params) (d : ℝ) :
    CtildeIntegral P 0 d = -(P.q * d) / 2 := by
  simp [CtildeIntegral]
  ring

/-- The integral representation is even in its first variable. -/
theorem CtildeIntegral_even (P : Params) (d : ℝ) :
    Function.Even (fun t => CtildeIntegral P t d) := by
  intro t
  simp [CtildeIntegral]

/--
Under positivity of the affine base on `[0,1]`, the integral and quotient
representations of `C̃` agree away from `t = 0`.
-/
theorem CtildeIntegral_eq_Ctilde_of_ne
    (P : Params) (t d : ℝ) (ht : t ≠ 0)
    (hpos : ∀ τ ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + τ * t ^ 2 * d) :
    CtildeIntegral P t d = Ctilde P t d := by
  let F : ℝ → ℝ := fun τ =>
    (1 - Real.rpow (1 + τ * t ^ 2 * d) (P.q / 2)) / t ^ 2
  let f : ℝ → ℝ := fun τ =>
    -(P.q * d / 2) * Real.rpow (1 + τ * t ^ 2 * d) ((P.q - 2) / 2)
  have hfcont : ContinuousOn f (Set.uIcc (0 : ℝ) 1) := by
    intro τ hτ
    have hτIcc : τ ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le zero_le_one] using hτ
    have hbasecont : ContinuousAt (fun s : ℝ => 1 + s * t ^ 2 * d) τ := by
      fun_prop
    exact (continuousAt_const.mul
      (hbasecont.rpow_const (Or.inl (ne_of_gt (hpos τ hτIcc))))).continuousWithinAt
  have hFTC : (∫ τ in (0 : ℝ)..1, f τ) = F 1 - F 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro τ hτ
      have hτIcc : τ ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le zero_le_one] using hτ
      have hone : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 τ := hasDerivAt_const τ 1
      have hid : HasDerivAt (fun s : ℝ => s) 1 τ := hasDerivAt_id τ
      have hbase := hone.add ((hid.mul_const (t ^ 2)).mul_const d)
      have hrpow := hbase.rpow_const (p := P.q / 2)
        (Or.inl (ne_of_gt (hpos τ hτIcc)))
      have hexponent : P.q / 2 - 1 = (P.q - 2) / 2 := by ring
      rw [hexponent] at hrpow
      have hraw := (hone.sub hrpow).div_const (t ^ 2)
      simp only [Pi.add_apply, Pi.sub_apply, one_mul, zero_add] at hraw
      have hvalue :
          (0 - t ^ 2 * d * (P.q / 2) *
              Real.rpow (1 + τ * t ^ 2 * d) ((P.q - 2) / 2)) / t ^ 2 =
            -(P.q * d / 2) *
              Real.rpow (1 + τ * t ^ 2 * d) ((P.q - 2) / 2) := by
        field_simp [ht]
        ring
      change HasDerivAt
        (fun s => (1 - Real.rpow (1 + s * t ^ 2 * d) (P.q / 2)) / t ^ 2)
        (-(P.q * d / 2) *
          Real.rpow (1 + τ * t ^ 2 * d) ((P.q - 2) / 2)) τ
      convert hraw.congr_deriv hvalue using 1 <;> rfl
    · exact hfcont.intervalIntegrable
  calc
    CtildeIntegral P t d = ∫ τ in (0 : ℝ)..1, f τ := by
      simp [CtildeIntegral, f]
    _ = F 1 - F 0 := hFTC
    _ = Ctilde P t d := by
      simp [F, Ctilde, ht]

end

end StressTensor
