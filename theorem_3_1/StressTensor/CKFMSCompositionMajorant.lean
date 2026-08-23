import StressTensor.CKAnalyticMajorant
import Mathlib.Analysis.Analytic.Composition

/-!
# Geometric bounds for formal analytic composition

The nonlinear part of the reduced CK system substitutes the formal solution
phase into analytic coefficient germs.  Mathlib already defines composition
of formal multilinear series and proves the sharp norm estimate for each
ordered composition of the homogeneous degree.  This file sums that estimate
and records a deliberately coarse, but geometric, bound.

The only combinatorics needed is that a positive integer `n` has
`2^(n-1)` ordered compositions.  Thus geometric bounds for the outer and
inner homogeneous coefficients remain geometric after substitution.
-/

namespace StressTensor

namespace CKFMSCompositionMajorant

noncomputable section

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Product of inner-series bounds along the blocks of a composition. -/
theorem prod_inner_bound
    {p : FormalMultilinearSeries ℝ E F} {D s : ℝ}
    (hp : ∀ k, ‖p k‖ ≤ D * s ^ k)
    {n : ℕ} (c : Composition n) :
    ∏ i, ‖p (c.blocksFun i)‖ ≤ D ^ c.length * s ^ n := by
  calc
    ∏ i, ‖p (c.blocksFun i)‖ ≤
        ∏ i, D * s ^ (c.blocksFun i) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact norm_nonneg _
      · intro i hi
        exact hp (c.blocksFun i)
    _ = D ^ c.length * s ^ n := by
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin,
        Finset.prod_pow_eq_pow_sum, c.sum_blocksFun]

/-- A single ordered-composition term is bounded uniformly by a geometric
quantity depending only on the total degree. -/
theorem compAlongComposition_norm_le_geometric
    {q : FormalMultilinearSeries ℝ F G}
    {p : FormalMultilinearSeries ℝ E F}
    {A r D s : ℝ}
    (hA : 0 ≤ A) (hr : 0 ≤ r) (hD : 0 ≤ D) (hs : 0 ≤ s)
    (hq : ∀ k, ‖q k‖ ≤ A * r ^ k)
    (hp : ∀ k, ‖p k‖ ≤ D * s ^ k)
    {n : ℕ} (c : Composition n) :
    ‖q.compAlongComposition p c‖ ≤
      A * (max 1 (r * D) * s) ^ n := by
  have hprod := prod_inner_bound hp c
  have hrD : 0 ≤ r * D := mul_nonneg hr hD
  have hT0 : 0 ≤ max 1 (r * D) := le_trans (by norm_num) (le_max_left _ _)
  have hpow : (r * D) ^ c.length ≤ (max 1 (r * D)) ^ n := by
    calc
      (r * D) ^ c.length ≤ (max 1 (r * D)) ^ c.length :=
        pow_le_pow_left₀ hrD (le_max_right _ _) _
      _ ≤ (max 1 (r * D)) ^ n :=
        pow_le_pow_right₀ (le_max_left _ _) c.length_le
  calc
    ‖q.compAlongComposition p c‖ ≤
        ‖q c.length‖ * ∏ i, ‖p (c.blocksFun i)‖ :=
      q.compAlongComposition_norm p c
    _ ≤ (A * r ^ c.length) * (D ^ c.length * s ^ n) := by
      exact mul_le_mul (hq c.length) hprod
        (Finset.prod_nonneg fun _ _ => norm_nonneg _)
        (mul_nonneg hA (pow_nonneg hr _))
    _ = A * (r * D) ^ c.length * s ^ n := by
      rw [mul_pow]
      ring
    _ ≤ A * (max 1 (r * D)) ^ n * s ^ n := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hA) (pow_nonneg hs _)
    _ = A * (max 1 (r * D) * s) ^ n := by
      rw [mul_pow]
      ring

/-- Geometric homogeneous-coefficient bounds are closed under Mathlib's
formal multilinear-series composition. -/
theorem norm_comp_le_geometric
    {q : FormalMultilinearSeries ℝ F G}
    {p : FormalMultilinearSeries ℝ E F}
    {A r D s : ℝ}
    (hA : 0 ≤ A) (hr : 0 ≤ r) (hD : 0 ≤ D) (hs : 0 ≤ s)
    (hq : ∀ k, ‖q k‖ ≤ A * r ^ k)
    (hp : ∀ k, ‖p k‖ ≤ D * s ^ k) :
    ∀ n, ‖q.comp p n‖ ≤
      A * (2 * max 1 (r * D) * s) ^ n := by
  intro n
  have hterm (c : Composition n) :
      ‖q.compAlongComposition p c‖ ≤
        A * (max 1 (r * D) * s) ^ n :=
    compAlongComposition_norm_le_geometric hA hr hD hs hq hp c
  have hcardNat : Fintype.card (Composition n) ≤ 2 ^ n := by
    rw [composition_card]
    exact Nat.pow_le_pow_right (by omega) (Nat.sub_le n 1)
  have hcard :
      (Fintype.card (Composition n) : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast hcardNat
  have hconst : 0 ≤ A * (max 1 (r * D) * s) ^ n := by
    positivity
  calc
    ‖q.comp p n‖ = ‖∑ c : Composition n, q.compAlongComposition p c‖ := rfl
    _ ≤ ∑ c : Composition n, ‖q.compAlongComposition p c‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _c : Composition n,
        A * (max 1 (r * D) * s) ^ n := by
      exact Finset.sum_le_sum fun c _ => hterm c
    _ = (Fintype.card (Composition n) : ℝ) *
        (A * (max 1 (r * D) * s) ^ n) := by
      simp [nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ n *
        (A * (max 1 (r * D) * s) ^ n) :=
      mul_le_mul_of_nonneg_right hcard hconst
    _ = A * (2 * max 1 (r * D) * s) ^ n := by
      rw [mul_pow]
      ring

/-! ## Specialization to packaged analytic germs -/

/-- Substituting a geometrically bounded formal phase into the quantitative
series of a `LocalAnalyticMajorant` gives an explicit geometric bound for
every homogeneous coefficient of the composite. -/
theorem LocalAnalyticMajorant.norm_comp_le_geometric
    {f : F → G} {x : F} (M : LocalAnalyticMajorant f x)
    (p : FormalMultilinearSeries ℝ E F)
    {D s : ℝ} (hD : 0 ≤ D) (hs : 0 ≤ s)
    (hp : ∀ k, ‖p k‖ ≤ D * s ^ k) :
    ∀ n, ‖M.series.comp p n‖ ≤
      M.coefficientBound *
        (2 * max 1 (((M.radius : ℝ)⁻¹) * D) * s) ^ n := by
  apply CKFMSCompositionMajorant.norm_comp_le_geometric
    M.coefficientBound_pos.le
    (inv_nonneg.mpr M.radius_real_pos.le) hD hs
  · intro k
    calc
      ‖M.series k‖ ≤ M.coefficientBound / (M.radius : ℝ) ^ k :=
        M.coeff_norm_le k
      _ = M.coefficientBound * ((M.radius : ℝ)⁻¹) ^ k := by
        rw [inv_pow]
        ring
  · exact hp

end

end CKFMSCompositionMajorant

end StressTensor
