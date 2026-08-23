import StressTensor.CKDiagonalMajorant

/-!
# A scalar Nagumo convolution kernel

The sequence `1 / (n+1)^2` is stable, up to an absolute constant, under
Cauchy convolution.  This file proves the elementary finite-sum estimates
needed to use that sequence as the scalar kernel in analytic
Cauchy--Kowalevskaya majorants.  It is independent of every equation-specific
formal recurrence.
-/

namespace StressTensor
namespace CKNagumoMajorant

open CKDiagonalMajorant
open scoped BigOperators

noncomputable section

/-- The scalar Nagumo kernel. -/
def nagumoCoeff (n : ℕ) : ℝ :=
  1 / (n + 1 : ℝ) ^ 2

@[simp] theorem nagumoCoeff_zero : nagumoCoeff 0 = 1 := by
  norm_num [nagumoCoeff]

theorem nagumoCoeff_pos (n : ℕ) : 0 < nagumoCoeff n := by
  unfold nagumoCoeff
  positivity

theorem nagumoCoeff_nonneg (n : ℕ) : 0 ≤ nagumoCoeff n :=
  (nagumoCoeff_pos n).le

/-- A telescoping majorant for one coefficient. -/
theorem nagumoCoeff_le_telescoping (n : ℕ) :
    nagumoCoeff n ≤
      2 * (1 / (n + 1 : ℝ) - 1 / (n + 2 : ℝ)) := by
  unfold nagumoCoeff
  have hn1 : 0 < (n + 1 : ℝ) := by positivity
  have hn2 : 0 < (n + 2 : ℝ) := by positivity
  field_simp
  nlinarith

theorem sum_range_telescoping (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (1 / (n + 1 : ℝ) - 1 / (n + 2 : ℝ))) =
        1 - 1 / (N + 1 : ℝ) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      push_cast
      ring

/-- Every finite partial sum of the Nagumo kernel is bounded by `2`. -/
theorem sum_range_nagumoCoeff_le_two (N : ℕ) :
    (∑ n ∈ Finset.range N, nagumoCoeff n) ≤ 2 := by
  calc
    (∑ n ∈ Finset.range N, nagumoCoeff n) ≤
        ∑ n ∈ Finset.range N,
          2 * (1 / (n + 1 : ℝ) - 1 / (n + 2 : ℝ)) := by
      exact Finset.sum_le_sum fun n hn => nagumoCoeff_le_telescoping n
    _ = 2 * (1 - 1 / (N + 1 : ℝ)) := by
      rw [← Finset.mul_sum, sum_range_telescoping]
    _ ≤ 2 := by
      have h : 0 ≤ 1 / (N + 1 : ℝ) := by positivity
      linarith

/-! ## Monotonicity of Cauchy convolution -/

/-- Cauchy convolution is monotone on nonnegative sequences. -/
theorem convolution_mono
    {u u' v v' : ℕ → ℝ}
    (hu0 : ∀ n, 0 ≤ u n) (hv0 : ∀ n, 0 ≤ v n)
    (hu : ∀ n, u n ≤ u' n) (hv : ∀ n, v n ≤ v' n) (n : ℕ) :
    convolution u v n ≤ convolution u' v' n := by
  unfold convolution
  apply Finset.sum_le_sum
  intro ij hij
  exact mul_le_mul (hu ij.1) (hv ij.2) (hv0 ij.2)
    ((hu0 ij.1).trans (hu ij.1))

theorem convolution_mono_left
    {u u' v : ℕ → ℝ}
    (hu0 : ∀ n, 0 ≤ u n) (hv0 : ∀ n, 0 ≤ v n)
    (hu : ∀ n, u n ≤ u' n) (n : ℕ) :
    convolution u v n ≤ convolution u' v n :=
  convolution_mono hu0 hv0 hu (fun _ => le_rfl) n

theorem convolution_mono_right
    {u v v' : ℕ → ℝ}
    (hu0 : ∀ n, 0 ≤ u n) (hv0 : ∀ n, 0 ≤ v n)
    (hv : ∀ n, v n ≤ v' n) (n : ℕ) :
    convolution u v n ≤ convolution u v' n :=
  convolution_mono hu0 hv0 (fun _ => le_rfl) hv n

theorem convolution_nonneg
    {u v : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (n : ℕ) :
    0 ≤ convolution u v n := by
  unfold convolution
  exact Finset.sum_nonneg fun ij hij => mul_nonneg (hu ij.1) (hv ij.2)

/-- A scalar factor can be pulled through the left input of convolution. -/
theorem convolution_const_mul_left
    (C : ℝ) (u v : ℕ → ℝ) (n : ℕ) :
    convolution (fun k => C * u k) v n = C * convolution u v n := by
  unfold convolution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  ring

/-! ## Quadratic and derivative-weighted stability -/

/-- The elementary real inequality underlying convolution stability. -/
private theorem nagumo_product_le
    {i j n : ℕ} (hij : i + j = n) :
    nagumoCoeff i * nagumoCoeff j ≤
      2 * nagumoCoeff n * (nagumoCoeff i + nagumoCoeff j) := by
  have hi : 0 < (i + 1 : ℝ) := by positivity
  have hj : 0 < (j + 1 : ℝ) := by positivity
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have hcast : (n : ℝ) = i + j := by exact_mod_cast hij.symm
  unfold nagumoCoeff
  field_simp
  nlinarith [sq_nonneg ((i + 1 : ℝ) - (j + 1 : ℝ))]

/-- The Nagumo kernel is stable under Cauchy convolution with the explicit
coarse constant `8`. -/
theorem convolution_nagumoCoeff_le (n : ℕ) :
    convolution nagumoCoeff nagumoCoeff n ≤ 8 * nagumoCoeff n := by
  unfold convolution
  calc
    (∑ ij ∈ Finset.antidiagonal n,
        nagumoCoeff ij.1 * nagumoCoeff ij.2) ≤
      ∑ ij ∈ Finset.antidiagonal n,
        2 * nagumoCoeff n *
          (nagumoCoeff ij.1 + nagumoCoeff ij.2) := by
      apply Finset.sum_le_sum
      intro ij hij
      exact nagumo_product_le (Finset.mem_antidiagonal.mp hij)
    _ = 4 * nagumoCoeff n *
        (∑ k ∈ Finset.range (n + 1), nagumoCoeff k) := by
      rw [show
        (∑ ij ∈ Finset.antidiagonal n,
          2 * nagumoCoeff n *
            (nagumoCoeff ij.1 + nagumoCoeff ij.2)) =
          ∑ k ∈ Finset.range (n + 1),
            2 * nagumoCoeff n *
              (nagumoCoeff k + nagumoCoeff (n - k)) by
        simpa using Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => 2 * nagumoCoeff n * (nagumoCoeff i + nagumoCoeff j)) n]
      have hreflect :
          (∑ k ∈ Finset.range (n + 1), nagumoCoeff (n - k)) =
            ∑ k ∈ Finset.range (n + 1), nagumoCoeff k := by
        simpa using Finset.sum_range_reflect (f := nagumoCoeff) (n := n + 1)
      rw [Finset.mul_sum]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        hreflect]
      rw [← Finset.mul_sum]
      ring
    _ ≤ 4 * nagumoCoeff n * 2 := by
      exact mul_le_mul_of_nonneg_left (sum_range_nagumoCoeff_le_two (n + 1))
        (mul_nonneg (by norm_num) (nagumoCoeff_nonneg n))
    _ = 8 * nagumoCoeff n := by ring

/-- Shifting the Nagumo index pays for one Euler derivative, up to the
explicit factor `2`. -/
theorem nat_mul_nagumoCoeff_le_two_succ (n : ℕ) :
    (n : ℝ) * nagumoCoeff n ≤
      2 * (n + 1 : ℝ) * nagumoCoeff (n + 1) := by
  unfold nagumoCoeff
  have hn1 : 0 < (n + 1 : ℝ) := by positivity
  have hn2 : 0 < (n + 2 : ℝ) := by positivity
  have hpoly :
      (n : ℝ) * (n + 2 : ℝ) ^ 2 ≤
        2 * (n + 1 : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg n)
      (sq_nonneg ((n : ℝ) + 1))]
  field_simp
  push_cast
  ring_nf at hpoly ⊢
  exact hpoly

/-- The derivative-weighted convolution appearing after `y ∂y` is
controlled by the integrated next Nagumo coefficient. -/
theorem weightedDerivativeConvolution_nagumoCoeff_le (n : ℕ) :
    (∑ ij ∈ Finset.antidiagonal n,
      nagumoCoeff ij.1 * (ij.2 : ℝ) * nagumoCoeff ij.2) ≤
        16 * (n + 1 : ℝ) * nagumoCoeff (n + 1) := by
  have hweighted :
      (∑ ij ∈ Finset.antidiagonal n,
        nagumoCoeff ij.1 * (ij.2 : ℝ) * nagumoCoeff ij.2) ≤
          (n : ℝ) * convolution nagumoCoeff nagumoCoeff n := by
    rw [convolution, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ij hij
    have hjn : ij.2 ≤ n := by
      have hadd := Finset.mem_antidiagonal.mp hij
      omega
    have hcast : (ij.2 : ℝ) ≤ n := by exact_mod_cast hjn
    calc
      nagumoCoeff ij.1 * (ij.2 : ℝ) * nagumoCoeff ij.2 =
          (ij.2 : ℝ) * (nagumoCoeff ij.1 * nagumoCoeff ij.2) := by ring
      _ ≤ (n : ℝ) * (nagumoCoeff ij.1 * nagumoCoeff ij.2) := by
        exact mul_le_mul_of_nonneg_right hcast
          (mul_nonneg (nagumoCoeff_nonneg _) (nagumoCoeff_nonneg _))
  calc
    (∑ ij ∈ Finset.antidiagonal n,
      nagumoCoeff ij.1 * (ij.2 : ℝ) * nagumoCoeff ij.2) ≤
        (n : ℝ) * convolution nagumoCoeff nagumoCoeff n := hweighted
    _ ≤ (n : ℝ) * (8 * nagumoCoeff n) := by
      exact mul_le_mul_of_nonneg_left (convolution_nagumoCoeff_le n)
        (Nat.cast_nonneg n)
    _ ≤ 8 * (2 * (n + 1 : ℝ) * nagumoCoeff (n + 1)) := by
      nlinarith [nat_mul_nagumoCoeff_le_two_succ n]
    _ = 16 * (n + 1 : ℝ) * nagumoCoeff (n + 1) := by ring

/-! ## Iterated convolution -/

/-- Repeated convolution with `u`; index `k` represents `k+1` factors. -/
def iteratedConvolution (u : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => u
  | k + 1 => convolution (iteratedConvolution u k) u

@[simp] theorem iteratedConvolution_zero (u : ℕ → ℝ) :
    iteratedConvolution u 0 = u := rfl

@[simp] theorem iteratedConvolution_succ (u : ℕ → ℝ) (k : ℕ) :
    iteratedConvolution u (k + 1) =
      convolution (iteratedConvolution u k) u := rfl

theorem iteratedConvolution_nonneg
    {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) :
    ∀ k n, 0 ≤ iteratedConvolution u k n := by
  intro k
  induction k with
  | zero => exact hu
  | succ k ih =>
      intro n
      exact convolution_nonneg ih hu n

/-- Every additional convolution by the Nagumo kernel costs at most a factor
of `8`. -/
theorem iteratedConvolution_nagumoCoeff_le (k n : ℕ) :
    iteratedConvolution nagumoCoeff k n ≤
      (8 : ℝ) ^ k * nagumoCoeff n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
      calc
        iteratedConvolution nagumoCoeff (k + 1) n =
            convolution (iteratedConvolution nagumoCoeff k)
              nagumoCoeff n := rfl
        _ ≤ convolution (fun j => (8 : ℝ) ^ k * nagumoCoeff j)
              nagumoCoeff n := by
          exact convolution_mono_left
            (iteratedConvolution_nonneg nagumoCoeff_nonneg k)
            nagumoCoeff_nonneg (fun j => ih j) n
        _ = (8 : ℝ) ^ k *
              convolution nagumoCoeff nagumoCoeff n :=
          convolution_const_mul_left _ _ _ _
        _ ≤ (8 : ℝ) ^ k * (8 * nagumoCoeff n) := by
          exact mul_le_mul_of_nonneg_left (convolution_nagumoCoeff_le n)
            (by positivity)
        _ = (8 : ℝ) ^ (k + 1) * nagumoCoeff n := by
          rw [pow_succ]
          ring

end

end CKNagumoMajorant
end StressTensor
