import StressTensor.CKDiagonalMajorant

/-!
# A coefficient majorant for first-order Fuchsian CK systems

After the reduction to the variables `(v,Gamma₂)`, the principal tangential
term has the form `y * N * U_y`.  On ordinary coefficients this contributes
`n * U[m,n]`, while integration in `x` divides by `m+1`.  The binomial weight
`choose (m+n) m` is exactly adapted to this apparent loss:

`n/(m+1) * choose (m+n) m = choose (m+n) (m+1)`.

This file formalizes that observation.  It applies to scalar bounds on any
finite-dimensional state (for example, the maximum of the two component
norms), so no order structure on the state space is required.
-/

namespace StressTensor

namespace CKFuchsianMajorant

open CKPowerSeries CKGeometricMajorant CKDiagonalMajorant

noncomputable section

/-- The binomial envelope naturally propagated by `y * d/dy` followed by
one zero-constant integration in `x`. -/
def transportEnvelope (K R S : ℝ) (m n : ℕ) : ℝ :=
  K * ((m + n).choose m : ℝ) * R ^ m * S ^ n

@[simp] theorem transportEnvelope_zero (K R S : ℝ) (n : ℕ) :
    transportEnvelope K R S 0 n = K * S ^ n := by
  simp [transportEnvelope]

/-- The exact ratio identity which absorbs the Euler derivative `y d/dy`. -/
theorem natCast_mul_choose_div_succ (m n : ℕ) :
    (n : ℝ) * ((m + n).choose m : ℝ) / (m + 1 : ℝ) =
      ((m + n).choose (m + 1) : ℝ) := by
  have hnat :
      (m + n).choose (m + 1) * (m + 1) =
        (m + n).choose m * n := by
    calc
      (m + n).choose (m + 1) * (m + 1) =
          (m + n).choose m * (m + n - m) :=
        Nat.choose_succ_right_eq (m + n) m
      _ = (m + n).choose m * n := by rw [Nat.add_sub_cancel_left]
  have hreal :
      ((m + n).choose (m + 1) : ℝ) * (m + 1 : ℝ) =
        ((m + n).choose m : ℝ) * (n : ℝ) := by
    exact_mod_cast hnat
  have hm : (m + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

/-- Pascal's identity in the indexing convention used by the transport
envelope. -/
theorem choose_transport_pascal (m n : ℕ) :
    (m + n + 1).choose (m + 1) =
      (m + n).choose m + (m + n).choose (m + 1) := by
  simpa [Nat.succ_eq_add_one] using Nat.choose_succ_succ (m + n) m

/-- A nonnegative scalar array satisfying the coefficient inequality for

`U_x = y N U_y + F`

is bounded by the binomial transport envelope.  Here `L` bounds the constant
principal matrix, while `f` is an already-majorized source.  The hypotheses
`L ≤ R` and `M ≤ K R` allocate the two Pascal summands to transport and
source respectively. -/
theorem le_transportEnvelope_of_recurrence
    {u f : Coeff} {K L M R S : ℝ}
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hLR : L ≤ R) (hMKR : M ≤ K * R)
    (hzero : ∀ n, u 0 n ≤ K * S ^ n)
    (hfbound : ∀ m n,
      f m n ≤ M * ((m + n).choose m : ℝ) * R ^ m * S ^ n)
    (hsucc : ∀ m n,
      u (m + 1) n ≤
        (L * (n : ℝ) * u m n + f m n) / (m + 1 : ℝ)) :
    ∀ m n, u m n ≤ transportEnvelope K R S m n := by
  intro m
  induction m with
  | zero =>
      intro n
      simpa using hzero n
  | succ m ih =>
      intro n
      have hm : 0 < (m + 1 : ℝ) := by positivity
      have htransport :
          (L * (n : ℝ) * transportEnvelope K R S m n) /
              (m + 1 : ℝ) ≤
            K * ((m + n).choose (m + 1) : ℝ) * R ^ (m + 1) * S ^ n := by
        rw [transportEnvelope]
        have hratio := natCast_mul_choose_div_succ m n
        calc
          (L * (n : ℝ) *
                (K * ((m + n).choose m : ℝ) * R ^ m * S ^ n)) /
              (m + 1 : ℝ) =
              L * K * (((n : ℝ) * ((m + n).choose m : ℝ)) /
                (m + 1 : ℝ)) * R ^ m * S ^ n := by ring
          _ = L * K * ((m + n).choose (m + 1) : ℝ) *
                R ^ m * S ^ n := by rw [hratio]
          _ = L * (K * ((m + n).choose (m + 1) : ℝ) *
                R ^ m * S ^ n) := by ring
          _ ≤ R * (K * ((m + n).choose (m + 1) : ℝ) *
                R ^ m * S ^ n) := by
              apply mul_le_mul_of_nonneg_right hLR
              positivity
          _ = R * K * ((m + n).choose (m + 1) : ℝ) *
                R ^ m * S ^ n := by ring
          _ = K * ((m + n).choose (m + 1) : ℝ) *
                R ^ (m + 1) * S ^ n := by rw [pow_succ]; ring
      have hsource :
          (M * ((m + n).choose m : ℝ) * R ^ m * S ^ n) /
              (m + 1 : ℝ) ≤
            K * ((m + n).choose m : ℝ) * R ^ (m + 1) * S ^ n := by
        have hdiv : M / (m + 1 : ℝ) ≤ K * R := by
          calc
            M / (m + 1 : ℝ) ≤ M := by
              exact div_le_self hM (by norm_num)
            _ ≤ K * R := hMKR
        calc
          (M * ((m + n).choose m : ℝ) * R ^ m * S ^ n) /
              (m + 1 : ℝ) =
              (M / (m + 1 : ℝ)) * ((m + n).choose m : ℝ) *
                R ^ m * S ^ n := by ring
          _ ≤ (K * R) * ((m + n).choose m : ℝ) * R ^ m * S ^ n := by
              simpa only [mul_assoc] using
                mul_le_mul_of_nonneg_right hdiv
                  (show 0 ≤ ((m + n).choose m : ℝ) * R ^ m * S ^ n by
                    positivity)
          _ = K * ((m + n).choose m : ℝ) * R ^ (m + 1) * S ^ n := by
              rw [pow_succ]
              ring
      calc
        u (m + 1) n ≤
            (L * (n : ℝ) * u m n + f m n) / (m + 1 : ℝ) := hsucc m n
        _ ≤ (L * (n : ℝ) * transportEnvelope K R S m n +
              M * ((m + n).choose m : ℝ) * R ^ m * S ^ n) /
              (m + 1 : ℝ) := by
            apply div_le_div_of_nonneg_right _ hm.le
            exact add_le_add
              (mul_le_mul_of_nonneg_left (ih n)
                (mul_nonneg hL (Nat.cast_nonneg _)))
              (hfbound m n)
        _ = (L * (n : ℝ) * transportEnvelope K R S m n) /
                (m + 1 : ℝ) +
              (M * ((m + n).choose m : ℝ) * R ^ m * S ^ n) /
                (m + 1 : ℝ) := by ring
        _ ≤ K * ((m + n).choose (m + 1) : ℝ) * R ^ (m + 1) * S ^ n +
              K * ((m + n).choose m : ℝ) * R ^ (m + 1) * S ^ n :=
            add_le_add htransport hsource
        _ = transportEnvelope K R S (m + 1) n := by
            rw [transportEnvelope, show m + 1 + n = m + n + 1 by omega,
              choose_transport_pascal]
            push_cast
            ring

/-- The binomial transport envelope yields the product-geometric certificate
used by the series realization modules. -/
theorem geometricBound_of_transport_recurrence
    {a u f : Coeff} {K L M R S : ℝ}
    (ha : ∀ m n, |a m n| ≤ u m n)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hLR : L ≤ R) (hMKR : M ≤ K * R)
    (hzero : ∀ n, u 0 n ≤ K * S ^ n)
    (hfbound : ∀ m n,
      f m n ≤ M * ((m + n).choose m : ℝ) * R ^ m * S ^ n)
    (hsucc : ∀ m n,
      u (m + 1) n ≤
        (L * (n : ℝ) * u m n + f m n) / (m + 1 : ℝ)) :
    GeometricBound a K (2 * R) (2 * S) := by
  refine ⟨hK, mul_nonneg (by norm_num) hR, mul_nonneg (by norm_num) hS, ?_⟩
  intro m n
  calc
    |a m n| ≤ u m n := ha m n
    _ ≤ transportEnvelope K R S m n :=
      le_transportEnvelope_of_recurrence hK hL hM hR hS hLR hMKR
        hzero hfbound hsucc m n
    _ ≤ K * (2 * R) ^ m * (2 * S) ^ n := by
      unfold transportEnvelope
      calc
        K * ((m + n).choose m : ℝ) * R ^ m * S ^ n
            ≤ K * (2 : ℝ) ^ (m + n) * R ^ m * S ^ n := by
              gcongr
              exact choose_cast_le_two_pow m n
        _ = K * (2 * R) ^ m * (2 * S) ^ n := by
          rw [pow_add, mul_pow, mul_pow]
          ring

/-! ## Quadratic diagonal closure

The nonlinear terms produced by analytic composition are most conveniently
estimated on total degree.  The following weighted lift turns the scalar
Cauchy convolution into the bivariate binomial envelope used above.  This is
the precise interface between a scalar Catalan estimate and the Fuchsian
transport recurrence.
-/

/-- The weighted diagonal lift of a scalar Cauchy convolution. -/
def diagonalConvolution (c d : ℕ → ℝ) (R S : ℝ) (m n : ℕ) : ℝ :=
  ((m + n).choose m : ℝ) * R ^ m * S ^ n * convolution c d (m + n)

/-- A binomial envelope with an arbitrary total-degree amplitude. -/
def diagonalTransportEnvelope (c : ℕ → ℝ) (R S : ℝ) (m n : ℕ) : ℝ :=
  ((m + n).choose m : ℝ) * R ^ m * S ^ n * c (m + n)

@[simp] theorem diagonalTransportEnvelope_zero
    (c : ℕ → ℝ) (R S : ℝ) (n : ℕ) :
    diagonalTransportEnvelope c R S 0 n = S ^ n * c n := by
  simp [diagonalTransportEnvelope]

/-- A convolution of nonnegative scalar sequences is nonnegative. -/
theorem convolution_nonneg {c d : ℕ → ℝ}
    (hc : ∀ k, 0 ≤ c k) (hd : ∀ k, 0 ≤ d k) (n : ℕ) :
    0 ≤ convolution c d n := by
  unfold convolution
  exact Finset.sum_nonneg fun ij _ => mul_nonneg (hc ij.1) (hd ij.2)

/-- The endpoint `(0,n)` gives a useful lower bound on a nonnegative
convolution. -/
theorem zero_mul_le_convolution {c d : ℕ → ℝ}
    (hc : ∀ k, 0 ≤ c k) (hd : ∀ k, 0 ≤ d k) (n : ℕ) :
    c 0 * d n ≤ convolution c d n := by
  unfold convolution
  exact Finset.single_le_sum
    (s := Finset.antidiagonal n)
    (f := fun ij : ℕ × ℕ => c ij.1 * d ij.2)
    (a := (0, n))
    (fun ij _ => mul_nonneg (hc ij.1) (hd ij.2)) (by simp)

/-- Abstract quadratic closure for the Fuchsian transport recurrence.

The amplitude `c` has two jobs.  The first scalar inequality pays for the
Euler transport term, and the second pays for both the quadratic convolution
and the remaining source.  Pascal's identity then advances the `x` row. -/
theorem le_diagonalTransportEnvelope_of_quadratic_recurrence
    {u f : Coeff} {c g : ℕ → ℝ} {L M R S : ℝ}
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hc : ∀ k, 0 ≤ c k)
    (hlinear : ∀ k, L * c k ≤ R * c (k + 1))
    (hquadratic : ∀ k,
      M * convolution c c k + g k ≤ R * c (k + 1))
    (hzero : ∀ n, u 0 n ≤ S ^ n * c n)
    (hfbound : ∀ m n,
      f m n ≤ ((m + n).choose m : ℝ) * R ^ m * S ^ n * g (m + n))
    (hsucc : ∀ m n,
      u (m + 1) n ≤
        (L * (n : ℝ) * u m n +
          M * diagonalConvolution c c R S m n + f m n) /
            (m + 1 : ℝ)) :
    ∀ m n, u m n ≤ diagonalTransportEnvelope c R S m n := by
  intro m
  induction m with
  | zero =>
      intro n
      simpa using hzero n
  | succ m ih =>
      intro n
      let B : ℝ := ((m + n).choose m : ℝ) * R ^ m * S ^ n
      have hB : 0 ≤ B := by
        dsimp [B]
        positivity
      have hm : 0 < (m + 1 : ℝ) := by positivity
      have htransport :
          (L * (n : ℝ) * diagonalTransportEnvelope c R S m n) /
              (m + 1 : ℝ) ≤
            ((m + n).choose (m + 1) : ℝ) * R ^ (m + 1) * S ^ n *
              c (m + n + 1) := by
        rw [diagonalTransportEnvelope]
        have hratio := natCast_mul_choose_div_succ m n
        calc
          (L * (n : ℝ) *
                (((m + n).choose m : ℝ) * R ^ m * S ^ n * c (m + n))) /
              (m + 1 : ℝ) =
              ((m + n).choose (m + 1) : ℝ) * R ^ m * S ^ n *
                (L * c (m + n)) := by rw [← hratio]; ring
          _ ≤ ((m + n).choose (m + 1) : ℝ) * R ^ m * S ^ n *
                (R * c (m + n + 1)) := by
              exact mul_le_mul_of_nonneg_left (hlinear (m + n)) (by positivity)
          _ = ((m + n).choose (m + 1) : ℝ) * R ^ (m + 1) * S ^ n *
                c (m + n + 1) := by rw [pow_succ]; ring
      have hsource0 :
          M * diagonalConvolution c c R S m n +
              B * g (m + n) ≤
            B * R * c (m + n + 1) := by
        dsimp [diagonalConvolution, B]
        calc
          M * (((m + n).choose m : ℝ) * R ^ m * S ^ n *
                convolution c c (m + n)) +
              (((m + n).choose m : ℝ) * R ^ m * S ^ n) * g (m + n) =
              (((m + n).choose m : ℝ) * R ^ m * S ^ n) *
                (M * convolution c c (m + n) + g (m + n)) := by ring
          _ ≤ (((m + n).choose m : ℝ) * R ^ m * S ^ n) *
                (R * c (m + n + 1)) := by
              exact mul_le_mul_of_nonneg_left (hquadratic (m + n)) (by positivity)
          _ = ((m + n).choose m : ℝ) * R ^ m * S ^ n * R *
                c (m + n + 1) := by ring
      have hsource :
          (M * diagonalConvolution c c R S m n + B * g (m + n)) /
              (m + 1 : ℝ) ≤
            ((m + n).choose m : ℝ) * R ^ (m + 1) * S ^ n *
              c (m + n + 1) := by
        have ht : 0 ≤ B * R * c (m + n + 1) :=
          mul_nonneg (mul_nonneg hB hR) (hc (m + n + 1))
        have hone : (1 : ℝ) ≤ (m + 1 : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
        rw [div_le_iff₀ hm]
        calc
          M * diagonalConvolution c c R S m n + B * g (m + n) ≤
              B * R * c (m + n + 1) := hsource0
          _ ≤ (B * R * c (m + n + 1)) * (m + 1 : ℝ) := by
              nlinarith
          _ = (((m + n).choose m : ℝ) * R ^ (m + 1) * S ^ n *
                c (m + n + 1)) * (m + 1 : ℝ) := by
              dsimp [B]
              rw [pow_succ]
              ring
      calc
        u (m + 1) n ≤
            (L * (n : ℝ) * u m n +
              M * diagonalConvolution c c R S m n + f m n) /
                (m + 1 : ℝ) := hsucc m n
        _ ≤ (L * (n : ℝ) * diagonalTransportEnvelope c R S m n +
              M * diagonalConvolution c c R S m n + B * g (m + n)) /
                (m + 1 : ℝ) := by
            apply div_le_div_of_nonneg_right _ hm.le
            have hfirst :
                L * (n : ℝ) * u m n ≤
                  L * (n : ℝ) * diagonalTransportEnvelope c R S m n :=
              mul_le_mul_of_nonneg_left (ih n)
                (mul_nonneg hL (Nat.cast_nonneg _))
            exact add_le_add (add_le_add hfirst (le_refl _))
              (by simpa [B] using hfbound m n)
        _ = (L * (n : ℝ) * diagonalTransportEnvelope c R S m n) /
                (m + 1 : ℝ) +
              (M * diagonalConvolution c c R S m n + B * g (m + n)) /
                (m + 1 : ℝ) := by ring
        _ ≤ ((m + n).choose (m + 1) : ℝ) * R ^ (m + 1) * S ^ n *
                c (m + n + 1) +
              ((m + n).choose m : ℝ) * R ^ (m + 1) * S ^ n *
                c (m + n + 1) := add_le_add htransport hsource
        _ = diagonalTransportEnvelope c R S (m + 1) n := by
            rw [diagonalTransportEnvelope,
              show m + 1 + n = m + n + 1 by omega, choose_transport_pascal]
            push_cast
            ring

/-- Catalan amplitudes simultaneously absorb the linear transport and the
quadratic source.  The conditions say that the Catalan scale `Q` is large
enough for both contributions. -/
theorem le_catalanTransportEnvelope_of_quadratic_recurrence
    {u f : Coeff} {K L M G Q R S : ℝ}
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hlinear : L ≤ R * K * Q)
    (hquadratic : M + G ≤ R * Q)
    (hzero : ∀ n, u 0 n ≤ S ^ n * catalanEnvelope K Q n)
    (hfbound : ∀ m n,
      f m n ≤ G * diagonalConvolution (catalanEnvelope K Q)
        (catalanEnvelope K Q) R S m n)
    (hsucc : ∀ m n,
      u (m + 1) n ≤
        (L * (n : ℝ) * u m n +
          M * diagonalConvolution (catalanEnvelope K Q)
            (catalanEnvelope K Q) R S m n + f m n) /
              (m + 1 : ℝ)) :
    ∀ m n, u m n ≤
      diagonalTransportEnvelope (catalanEnvelope K Q) R S m n := by
  let c := catalanEnvelope K Q
  have hc : ∀ k, 0 ≤ c k := fun k => catalanEnvelope_nonneg hK hQ k
  have hlin : ∀ k, L * c k ≤ R * c (k + 1) := by
    intro k
    have hend : K * c k ≤ convolution c c k := by
      simpa [c, catalanEnvelope_zero] using zero_mul_le_convolution hc hc k
    calc
      L * c k ≤ (R * K * Q) * c k :=
        mul_le_mul_of_nonneg_right hlinear (hc k)
      _ = (R * Q) * (K * c k) := by ring
      _ ≤ (R * Q) * convolution c c k :=
        mul_le_mul_of_nonneg_left hend (mul_nonneg hR hQ)
      _ = R * c (k + 1) := by
        rw [show c (k + 1) = Q * convolution c c k by
          simpa [c] using catalanEnvelope_succ K Q k]
        ring
  have hquad : ∀ k,
      M * convolution c c k + G * convolution c c k ≤ R * c (k + 1) := by
    intro k
    have hconv := convolution_nonneg hc hc k
    calc
      M * convolution c c k + G * convolution c c k =
          (M + G) * convolution c c k := by ring
      _ ≤ (R * Q) * convolution c c k :=
        mul_le_mul_of_nonneg_right hquadratic hconv
      _ = R * c (k + 1) := by
        rw [show c (k + 1) = Q * convolution c c k by
          simpa [c] using catalanEnvelope_succ K Q k]
        ring
  apply le_diagonalTransportEnvelope_of_quadratic_recurrence
    (u := u) (f := f) (c := c) (g := fun k => G * convolution c c k)
    hL hR hS hc hlin hquad hzero
  · intro m n
    have hf := hfbound m n
    dsimp [diagonalConvolution, c] at hf ⊢
    exact hf.trans_eq (by ring)
  · simpa [c] using hsucc

/-- The Catalan transport closure gives an explicit product-geometric
convergence certificate. -/
theorem geometricBound_of_catalan_transport_recurrence
    {a u f : Coeff} {K L M G Q R S : ℝ}
    (ha : ∀ m n, |a m n| ≤ u m n)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hlinear : L ≤ R * K * Q)
    (hquadratic : M + G ≤ R * Q)
    (hzero : ∀ n, u 0 n ≤ S ^ n * catalanEnvelope K Q n)
    (hfbound : ∀ m n,
      f m n ≤ G * diagonalConvolution (catalanEnvelope K Q)
        (catalanEnvelope K Q) R S m n)
    (hsucc : ∀ m n,
      u (m + 1) n ≤
        (L * (n : ℝ) * u m n +
          M * diagonalConvolution (catalanEnvelope K Q)
            (catalanEnvelope K Q) R S m n + f m n) /
              (m + 1 : ℝ)) :
    GeometricBound a K (8 * (K * Q) * R) (8 * (K * Q) * S) := by
  have hu := le_catalanTransportEnvelope_of_quadratic_recurrence
    hK hL hQ hR hS hlinear hquadratic hzero hfbound hsucc
  refine ⟨hK, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · intro m n
    calc
      |a m n| ≤ u m n := ha m n
      _ ≤ diagonalTransportEnvelope (catalanEnvelope K Q) R S m n := hu m n
      _ ≤ ((m + n).choose m : ℝ) * R ^ m * S ^ n *
            (K * (4 * (K * Q)) ^ (m + n)) := by
          unfold diagonalTransportEnvelope
          exact mul_le_mul_of_nonneg_left
            (catalanEnvelope_le_geometric hK hQ (m + n)) (by positivity)
      _ ≤ (2 : ℝ) ^ (m + n) * R ^ m * S ^ n *
            (K * (4 * (K * Q)) ^ (m + n)) := by
          gcongr
          exact choose_cast_le_two_pow m n
      _ = K * (8 * (K * Q) * R) ^ m * (8 * (K * Q) * S) ^ n := by
          have hm8 : (8 : ℝ) ^ m = 2 ^ m * 4 ^ m := by
            rw [← mul_pow]
            norm_num
          have hn8 : (8 : ℝ) ^ n = 2 ^ n * 4 ^ n := by
            rw [← mul_pow]
            norm_num
          simp only [pow_add, mul_pow]
          rw [hm8, hn8]
          ring

end

end CKFuchsianMajorant

end StressTensor
