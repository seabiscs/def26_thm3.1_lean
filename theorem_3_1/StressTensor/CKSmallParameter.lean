import StressTensor.CKFMSNagumoComposition

/-!
# A common small parameter for two analytic compositions

The reduced principal matrix and source have possibly different analytic
radii.  This file chooses one explicit positive amplitude that lies inside
both Nagumo composition thresholds.
-/

namespace StressTensor
namespace CKSmallParameter

noncomputable section

/-- An explicit positive amplitude small enough for two nonnegative inverse
radii. -/
def commonSmallEpsilon (r s : ℝ) : ℝ :=
  (32 * (1 + r + s))⁻¹

theorem commonSmallEpsilon_pos
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    0 < commonSmallEpsilon r s := by
  unfold commonSmallEpsilon
  positivity

theorem commonSmallEpsilon_first
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    8 * (commonSmallEpsilon r s * r) < 1 := by
  let d : ℝ := 32 * (1 + r + s)
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hnum : 8 * r < d := by
    dsimp [d]
    nlinarith
  unfold commonSmallEpsilon
  change 8 * ((32 * (1 + r + s))⁻¹ * r) < 1
  rw [show 32 * (1 + r + s) = d by rfl]
  rw [inv_mul_eq_div]
  rw [show 8 * (r / d) = (8 * r) / d by ring]
  rw [div_lt_one hd]
  exact hnum

theorem commonSmallEpsilon_second
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    8 * (commonSmallEpsilon r s * s) < 1 := by
  let d : ℝ := 32 * (1 + r + s)
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hnum : 8 * s < d := by
    dsimp [d]
    nlinarith
  unfold commonSmallEpsilon
  change 8 * ((32 * (1 + r + s))⁻¹ * s) < 1
  rw [show 32 * (1 + r + s) = d by rfl]
  rw [inv_mul_eq_div]
  rw [show 8 * (s / d) = (8 * s) / d by ring]
  rw [div_lt_one hd]
  exact hnum

/-- Tangential geometric rate making the normalized linear `y` coordinate
fit the first Nagumo coefficient (`nagumoCoeff 1 = 1/4`). -/
def tangentialRate (epsilon : ℝ) : ℝ := 4 / epsilon

theorem tangentialRate_pos {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < tangentialRate epsilon := by
  unfold tangentialRate
  positivity

theorem inv_tangentialRate_eq_nagumo
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (tangentialRate epsilon)⁻¹ =
      epsilon * CKNagumoMajorant.nagumoCoeff 1 := by
  unfold tangentialRate CKNagumoMajorant.nagumoCoeff
  norm_num
  field_simp

/-- The positive-degree composition constant associated to a geometric
outer bound `A * r^k`. -/
def nagumoCompositionConstant (A r epsilon : ℝ) : ℝ :=
  A * ((epsilon * r) / (1 - 8 * (epsilon * r)))

/-- The composition constant with the inner amplitude factored out. -/
def nagumoCompositionSlope (A r epsilon : ℝ) : ℝ :=
  A * (r / (1 - 8 * (epsilon * r)))

theorem nagumoCompositionConstant_eq_slope_mul
    (A r epsilon : ℝ) :
    nagumoCompositionConstant A r epsilon =
      nagumoCompositionSlope A r epsilon * epsilon := by
  unfold nagumoCompositionConstant nagumoCompositionSlope
  ring

theorem nagumoCompositionConstant_nonneg
    {A r epsilon : ℝ}
    (hA : 0 ≤ A) (hr : 0 ≤ r) (hepsilon : 0 ≤ epsilon)
    (hsmall : 8 * (epsilon * r) < 1) :
    0 ≤ nagumoCompositionConstant A r epsilon := by
  unfold nagumoCompositionConstant
  exact mul_nonneg hA
    (div_nonneg (mul_nonneg hepsilon hr) (sub_nonneg.mpr hsmall.le))

theorem nagumoCompositionSlope_nonneg
    {A r epsilon : ℝ}
    (hA : 0 ≤ A) (hr : 0 ≤ r)
    (hsmall : 8 * (epsilon * r) < 1) :
    0 ≤ nagumoCompositionSlope A r epsilon := by
  unfold nagumoCompositionSlope
  exact mul_nonneg hA
    (div_nonneg hr (sub_nonneg.mpr hsmall.le))

end
end CKSmallParameter
end StressTensor
