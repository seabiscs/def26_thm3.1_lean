import StressTensor.CKFuchsianMajorant

/-!
# Stable total-degree majorants for Fuchsian CK recurrences

This module isolates the binomial identity that absorbs one tangential
derivative after the zero-Cauchy integration in `x`.  Unlike a purely
geometric estimate, the scalar amplitude may vary with total degree; this is
the interface needed by convolution-stable (Nagumo) analytic majorants.
-/

namespace StressTensor
namespace CKStableTransportMajorant

open CKPowerSeries CKGeometricMajorant CKDiagonalMajorant
  CKFuchsianMajorant

noncomputable section

/-- A total-degree source estimate closes a Fuchsian row recurrence when its
combined linear/source amplitude advances the scalar degree majorant. -/
theorem le_diagonalTransportEnvelope_of_degree_recurrence
    {u f : Coeff} {c g : ℕ → ℝ} {L R S : ℝ}
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hc : ∀ k, 0 ≤ c k)
    (hstep : ∀ k : ℕ,
      L * (k : ℝ) * c k + g k ≤ ((k + 1 : ℕ) : ℝ) * R * c (k + 1))
    (hzero : ∀ n, u 0 n ≤ S ^ n * c n)
    (hfbound : ∀ m n,
      f m n ≤ ((m + n).choose m : ℝ) * R ^ m * S ^ n * g (m + n))
    (hsucc : ∀ m n,
      u (m + 1) n ≤
        (L * (n : ℝ) * u m n + f m n) / (m + 1 : ℝ)) :
    ∀ m n, u m n ≤ diagonalTransportEnvelope c R S m n := by
  intro m
  induction m with
  | zero =>
      intro n
      simpa [diagonalTransportEnvelope] using hzero n
  | succ m ih =>
      intro n
      let k := m + n
      let B : ℝ := ((m + n).choose m : ℝ) * R ^ m * S ^ n
      have hB : 0 ≤ B := by
        dsimp [B]
        positivity
      have hm : 0 < (m + 1 : ℝ) := by positivity
      have hnk : (n : ℝ) ≤ (k : ℝ) := by
        dsimp [k]
        exact_mod_cast Nat.le_add_left n m
      have hlin :
          L * (n : ℝ) * c k + g k ≤
            ((k + 1 : ℕ) : ℝ) * R * c (k + 1) := by
        calc
          L * (n : ℝ) * c k + g k ≤
              L * (k : ℝ) * c k + g k := by
            have ht : L * (n : ℝ) * c k ≤ L * (k : ℝ) * c k := by
              calc
                L * (n : ℝ) * c k = (n : ℝ) * (L * c k) := by ring
                _ ≤ (k : ℝ) * (L * c k) :=
                  mul_le_mul_of_nonneg_right hnk (mul_nonneg hL (hc k))
                _ = L * (k : ℝ) * c k := by ring
            linarith
          _ ≤ ((k + 1 : ℕ) : ℝ) * R * c (k + 1) := hstep k
      have hchooseNat :
          (m + 1) * (m + n + 1).choose (m + 1) =
            (m + n + 1) * (m + n).choose m :=
        CKDiagonalMajorant.succ_mul_choose_succ_left m n
      have hchoose :
          (m + 1 : ℝ) * ((m + n + 1).choose (m + 1) : ℝ) =
            (m + n + 1 : ℝ) * ((m + n).choose m : ℝ) := by
        exact_mod_cast hchooseNat
      calc
        u (m + 1) n ≤
            (L * (n : ℝ) * u m n + f m n) / (m + 1 : ℝ) :=
          hsucc m n
        _ ≤ (L * (n : ℝ) * diagonalTransportEnvelope c R S m n +
              B * g (m + n)) / (m + 1 : ℝ) := by
          apply div_le_div_of_nonneg_right _ hm.le
          exact add_le_add
            (mul_le_mul_of_nonneg_left (ih n)
              (mul_nonneg hL (Nat.cast_nonneg n)))
            (by simpa [B] using hfbound m n)
        _ = B * (L * (n : ℝ) * c k + g k) / (m + 1 : ℝ) := by
          dsimp [B, k]
          simp only [diagonalTransportEnvelope]
          ring
        _ ≤ B * (((k + 1 : ℕ) : ℝ) * R * c (k + 1)) /
              (m + 1 : ℝ) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlin hB) hm.le
        _ = diagonalTransportEnvelope c R S (m + 1) n := by
          dsimp [B, k]
          simp only [diagonalTransportEnvelope]
          rw [show m + 1 + n = m + n + 1 by omega]
          have hm0 : (m + 1 : ℝ) ≠ 0 := ne_of_gt hm
          rw [div_eq_iff hm0]
          rw [pow_succ]
          calc
            (((m + n).choose m : ℝ) * R ^ m * S ^ n) *
                (((m + n + 1 : ℕ) : ℝ) * R * c (m + n + 1)) =
                ((m + n + 1 : ℝ) * ((m + n).choose m : ℝ)) *
                  R ^ m * R * S ^ n * c (m + n + 1) := by
              push_cast
              ring
            _ = ((m + 1 : ℝ) *
                  ((m + n + 1).choose (m + 1) : ℝ)) *
                  R ^ m * R * S ^ n * c (m + n + 1) := by rw [hchoose]
            _ = ((m + n + 1).choose (m + 1) : ℝ) *
                  (R ^ m * R) * S ^ n * c (m + n + 1) *
                    (m + 1 : ℝ) := by ring

/-- Vector form of the stable transport recurrence.  It converts the exact
coefficient equality into the scalar norm inequality consumed above. -/
theorem norm_le_diagonalTransportEnvelope_of_vector_recurrence
    {ι : Type*} [Fintype ι]
    {a transport nonlinear : ℕ → ℕ → (ι → ℝ)}
    {c g : ℕ → ℝ} {L R S : ℝ}
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hc : ∀ k, 0 ≤ c k)
    (hstep : ∀ k : ℕ,
      L * (k : ℝ) * c k + g k ≤ ((k + 1 : ℕ) : ℝ) * R * c (k + 1))
    (hzero : ∀ n, ‖a 0 n‖ ≤ S ^ n * c n)
    (htransport : ∀ m n, ‖transport m n‖ ≤ L * ‖a m n‖)
    (hnonlinear : ∀ m n,
      ‖nonlinear m n‖ ≤
        ((m + n).choose m : ℝ) * R ^ m * S ^ n * g (m + n))
    (hrec : ∀ m n,
      ((m + 1 : ℕ) : ℝ) • a (m + 1) n =
        (n : ℝ) • transport m n + nonlinear m n) :
    ∀ m n, ‖a m n‖ ≤ diagonalTransportEnvelope c R S m n := by
  apply le_diagonalTransportEnvelope_of_degree_recurrence
    (u := fun m n => ‖a m n‖) (f := fun m n => ‖nonlinear m n‖)
    hL hR hS hc hstep hzero hnonlinear
  intro m n
  have hm : 0 < (m + 1 : ℝ) := by positivity
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hscaled :
      (m + 1 : ℝ) * ‖a (m + 1) n‖ ≤
        L * (n : ℝ) * ‖a m n‖ + ‖nonlinear m n‖ := by
    calc
      (m + 1 : ℝ) * ‖a (m + 1) n‖ =
          ‖(m + 1 : ℝ) • a (m + 1) n‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hm]
      _ = ‖(n : ℝ) • transport m n + nonlinear m n‖ := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          congrArg norm (hrec m n)
      _ ≤ ‖(n : ℝ) • transport m n‖ + ‖nonlinear m n‖ :=
        norm_add_le _ _
      _ = (n : ℝ) * ‖transport m n‖ + ‖nonlinear m n‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hn]
      _ ≤ (n : ℝ) * (L * ‖a m n‖) + ‖nonlinear m n‖ :=
        add_le_add
          (mul_le_mul_of_nonneg_left (htransport m n) hn) le_rfl
      _ = L * (n : ℝ) * ‖a m n‖ + ‖nonlinear m n‖ := by ring
  rw [le_div_iff₀ hm]
  nlinarith

/-- A geometric upper bound for the scalar total-degree amplitude turns a
diagonal transport envelope into a separable bivariate geometric bound. -/
theorem geometricBound_component_of_norm_le_diagonalTransportEnvelope
    {ι : Type*} [Fintype ι]
    {a : ℕ → ℕ → (ι → ℝ)} {c : ℕ → ℝ}
    {C T R S : ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hc : ∀ k, c k ≤ C * T ^ k)
    (ha : ∀ m n, ‖a m n‖ ≤ diagonalTransportEnvelope c R S m n)
    (i : ι) :
    GeometricBound (fun m n => a m n i) C (2 * T * R) (2 * T * S) := by
  refine ⟨hC, by positivity, by positivity, ?_⟩
  intro m n
  calc
    |a m n i| ≤ ‖a m n‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (a m n) i
    _ ≤ diagonalTransportEnvelope c R S m n := ha m n
    _ ≤ ((m + n).choose m : ℝ) * R ^ m * S ^ n *
          (C * T ^ (m + n)) := by
      unfold diagonalTransportEnvelope
      exact mul_le_mul_of_nonneg_left (hc (m + n)) (by positivity)
    _ ≤ (2 : ℝ) ^ (m + n) * R ^ m * S ^ n *
          (C * T ^ (m + n)) := by
      gcongr
      exact CKDiagonalMajorant.choose_cast_le_two_pow m n
    _ = C * (2 * T * R) ^ m * (2 * T * S) ^ n := by
      simp only [pow_add, mul_pow]
      ring

/-- Truncate a bivariate coefficient array after a fixed total degree. -/
def truncateTotal
    {E : Type*} [Zero E] (k : ℕ) (a : ℕ → ℕ → E) : ℕ → ℕ → E :=
  fun m n => if m + n ≤ k then a m n else 0

@[simp] theorem truncateTotal_eq
    {E : Type*} [Zero E] {k m n : ℕ} {a : ℕ → ℕ → E}
    (h : m + n ≤ k) : truncateTotal k a m n = a m n := by
  simp [truncateTotal, h]

@[simp] theorem truncateTotal_eq_zero
    {E : Type*} [Zero E] {k m n : ℕ} {a : ℕ → ℕ → E}
    (h : ¬m + n ≤ k) : truncateTotal k a m n = 0 := by
  simp [truncateTotal, h]

/-- A causal nonlinear residual can be estimated on a globally bounded
truncation.  Strong induction then closes the desired bound for the original
formal solution without a circular global majorant hypothesis. -/
theorem norm_le_diagonalTransportEnvelope_of_causal_vector_recurrence
    {ι : Type*} [Fintype ι]
    {a : ℕ → ℕ → (ι → ℝ)}
    {transport : ℕ → ℕ → (ι → ℝ)}
    {nonlinear : (ℕ → ℕ → (ι → ℝ)) → ℕ → ℕ → (ι → ℝ)}
    {c g : ℕ → ℝ} {L R S : ℝ}
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hc : ∀ k, 0 ≤ c k)
    (hstep : ∀ k : ℕ,
      L * (k : ℝ) * c k + g k ≤ ((k + 1 : ℕ) : ℝ) * R * c (k + 1))
    (hzero : ∀ n, ‖a 0 n‖ ≤ S ^ n * c n)
    (htransport : ∀ m n, ‖transport m n‖ ≤ L * ‖a m n‖)
    (hcausal : ∀ {u v m n},
      (∀ i j, i + j ≤ m + n → u i j = v i j) →
        nonlinear u m n = nonlinear v m n)
    (hnonlinear : ∀ u,
      (∀ i j, ‖u i j‖ ≤ diagonalTransportEnvelope c R S i j) →
      ∀ m n,
        ‖nonlinear u m n‖ ≤
          ((m + n).choose m : ℝ) * R ^ m * S ^ n * g (m + n))
    (hrec : ∀ m n,
      ((m + 1 : ℕ) : ℝ) • a (m + 1) n =
        (n : ℝ) • transport m n + nonlinear a m n) :
    ∀ m n, ‖a m n‖ ≤ diagonalTransportEnvelope c R S m n := by
  intro m n
  have H : ∀ d i j, i + j = d →
      ‖a i j‖ ≤ diagonalTransportEnvelope c R S i j := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro i j hij
        cases i with
        | zero =>
            simpa [diagonalTransportEnvelope] using hzero j
        | succ i =>
            let k := i + j
            let u := truncateTotal k a
            have hdk : k < d := by
              dsimp [k]
              omega
            have hu : ∀ r s,
                ‖u r s‖ ≤ diagonalTransportEnvelope c R S r s := by
              intro r s
              by_cases hrs : r + s ≤ k
              · rw [show u r s = a r s by simp [u, hrs]]
                exact ih (r + s) (hrs.trans_lt hdk) r s rfl
              · rw [show u r s = 0 by simp [u, hrs], norm_zero]
                unfold diagonalTransportEnvelope
                exact mul_nonneg
                  (mul_nonneg
                    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hR _))
                    (pow_nonneg hS _))
                  (hc (r + s))
            have hresU := hnonlinear u hu i j
            have hresEq : nonlinear a i j = nonlinear u i j := by
              apply hcausal
              intro r s hrs
              exact (truncateTotal_eq (a := a) hrs).symm
            have hres :
                ‖nonlinear a i j‖ ≤
                  ((i + j).choose i : ℝ) * R ^ i * S ^ j * g (i + j) := by
              rw [hresEq]
              exact hresU
            have hprev :
                ‖a i j‖ ≤ diagonalTransportEnvelope c R S i j :=
              ih (i + j) hdk i j rfl
            have hi : 0 < (i + 1 : ℝ) := by positivity
            have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
            have hscaled :
                (i + 1 : ℝ) * ‖a (i + 1) j‖ ≤
                  L * (j : ℝ) * ‖a i j‖ + ‖nonlinear a i j‖ := by
              calc
                (i + 1 : ℝ) * ‖a (i + 1) j‖ =
                    ‖(i + 1 : ℝ) • a (i + 1) j‖ := by
                  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hi]
                _ = ‖(j : ℝ) • transport i j + nonlinear a i j‖ := by
                  simpa only [Nat.cast_add, Nat.cast_one] using
                    congrArg norm (hrec i j)
                _ ≤ ‖(j : ℝ) • transport i j‖ + ‖nonlinear a i j‖ :=
                  norm_add_le _ _
                _ = (j : ℝ) * ‖transport i j‖ + ‖nonlinear a i j‖ := by
                  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hj]
                _ ≤ (j : ℝ) * (L * ‖a i j‖) + ‖nonlinear a i j‖ :=
                  add_le_add
                    (mul_le_mul_of_nonneg_left (htransport i j) hj) le_rfl
                _ = L * (j : ℝ) * ‖a i j‖ + ‖nonlinear a i j‖ := by ring
            have hsuccNorm :
                ‖a (i + 1) j‖ ≤
                  (L * (j : ℝ) * ‖a i j‖ + ‖nonlinear a i j‖) /
                    (i + 1 : ℝ) := by
              rw [le_div_iff₀ hi]
              simpa only [mul_comm] using hscaled
            let B : ℝ := ((i + j).choose i : ℝ) * R ^ i * S ^ j
            have hB : 0 ≤ B := by
              dsimp [B]
              positivity
            have hjk : (j : ℝ) ≤ (k : ℝ) := by
              dsimp [k]
              exact_mod_cast Nat.le_add_left j i
            have hamp :
                L * (j : ℝ) * c k + g k ≤
                  ((k + 1 : ℕ) : ℝ) * R * c (k + 1) := by
              calc
                L * (j : ℝ) * c k + g k ≤
                    L * (k : ℝ) * c k + g k := by
                  have ht : L * (j : ℝ) * c k ≤ L * (k : ℝ) * c k := by
                    calc
                      L * (j : ℝ) * c k = (j : ℝ) * (L * c k) := by ring
                      _ ≤ (k : ℝ) * (L * c k) :=
                        mul_le_mul_of_nonneg_right hjk (mul_nonneg hL (hc k))
                      _ = L * (k : ℝ) * c k := by ring
                  linarith
                _ ≤ ((k + 1 : ℕ) : ℝ) * R * c (k + 1) := hstep k
            have hchooseNat :
                (i + 1) * (i + j + 1).choose (i + 1) =
                  (i + j + 1) * (i + j).choose i :=
              CKDiagonalMajorant.succ_mul_choose_succ_left i j
            have hchoose :
                (i + 1 : ℝ) * ((i + j + 1).choose (i + 1) : ℝ) =
                  (i + j + 1 : ℝ) * ((i + j).choose i : ℝ) := by
              exact_mod_cast hchooseNat
            calc
              ‖a (i + 1) j‖ ≤
                  (L * (j : ℝ) * ‖a i j‖ + ‖nonlinear a i j‖) /
                    (i + 1 : ℝ) := hsuccNorm
              _ ≤ (L * (j : ℝ) * diagonalTransportEnvelope c R S i j +
                    B * g (i + j)) / (i + 1 : ℝ) := by
                apply div_le_div_of_nonneg_right _ hi.le
                exact add_le_add
                  (mul_le_mul_of_nonneg_left hprev
                    (mul_nonneg hL (Nat.cast_nonneg j)))
                  (by simpa [B] using hres)
              _ = B * (L * (j : ℝ) * c k + g k) / (i + 1 : ℝ) := by
                dsimp [B, k]
                simp only [diagonalTransportEnvelope]
                ring
              _ ≤ B * (((k + 1 : ℕ) : ℝ) * R * c (k + 1)) /
                    (i + 1 : ℝ) := by
                exact div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hamp hB) hi.le
              _ = diagonalTransportEnvelope c R S (i + 1) j := by
                dsimp [B, k]
                simp only [diagonalTransportEnvelope]
                rw [show i + 1 + j = i + j + 1 by omega]
                have hi0 : (i + 1 : ℝ) ≠ 0 := ne_of_gt hi
                rw [div_eq_iff hi0, pow_succ]
                calc
                  (((i + j).choose i : ℝ) * R ^ i * S ^ j) *
                      (((i + j + 1 : ℕ) : ℝ) * R * c (i + j + 1)) =
                      ((i + j + 1 : ℝ) * ((i + j).choose i : ℝ)) *
                        R ^ i * R * S ^ j * c (i + j + 1) := by
                    push_cast
                    ring
                  _ = ((i + 1 : ℝ) *
                        ((i + j + 1).choose (i + 1) : ℝ)) *
                        R ^ i * R * S ^ j * c (i + j + 1) := by rw [hchoose]
                  _ = ((i + j + 1).choose (i + 1) : ℝ) *
                        (R ^ i * R) * S ^ j * c (i + j + 1) *
                          (i + 1 : ℝ) := by ring
  exact H (m + n) m n rfl

/-! ## Preserving a forced zero constant coefficient -/

/-- Replace the constant bivariate coefficient by zero and leave every
other coefficient unchanged.  This is useful for zero-Cauchy CK systems:
all total-degree truncations of their formal solution retain this invariant. -/
def zeroOrigin
    {E : Type*} [Zero E] (u : ℕ → ℕ → E) : ℕ → ℕ → E :=
  fun m n => if m = 0 ∧ n = 0 then 0 else u m n

@[simp] theorem zeroOrigin_zero_zero
    {E : Type*} [Zero E] (u : ℕ → ℕ → E) :
    zeroOrigin u 0 0 = 0 := by
  simp [zeroOrigin]

theorem zeroOrigin_eq
    {E : Type*} [Zero E] {u : ℕ → ℕ → E}
    (hu : u 0 0 = 0) : zeroOrigin u = u := by
  funext m n
  by_cases h : m = 0 ∧ n = 0
  · rcases h with ⟨rfl, rfl⟩
    simp [zeroOrigin, hu]
  · simp [zeroOrigin, h]

/-- Zero-origin version of
`norm_le_diagonalTransportEnvelope_of_causal_vector_recurrence`.

The nonlinear estimate is required only for coefficient arrays whose
constant coefficient is zero.  This is not an extra analytic assumption:
the wrapper applies the preceding theorem to `zeroOrigin u`, and the exact
recurrence identifies this with the original array using `ha00`. -/
theorem norm_le_diagonalTransportEnvelope_of_causal_vector_recurrence_zeroOrigin
    {ι : Type*} [Fintype ι]
    {a : ℕ → ℕ → (ι → ℝ)}
    {transport : ℕ → ℕ → (ι → ℝ)}
    {nonlinear : (ℕ → ℕ → (ι → ℝ)) → ℕ → ℕ → (ι → ℝ)}
    {c g : ℕ → ℝ} {L R S : ℝ}
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hc : ∀ k, 0 ≤ c k)
    (hstep : ∀ k : ℕ,
      L * (k : ℝ) * c k + g k ≤ ((k + 1 : ℕ) : ℝ) * R * c (k + 1))
    (hzero : ∀ n, ‖a 0 n‖ ≤ S ^ n * c n)
    (ha00 : a 0 0 = 0)
    (htransport : ∀ m n, ‖transport m n‖ ≤ L * ‖a m n‖)
    (hcausal : ∀ {u v m n},
      (∀ i j, i + j ≤ m + n → u i j = v i j) →
        nonlinear u m n = nonlinear v m n)
    (hnonlinear : ∀ u, u 0 0 = 0 →
      (∀ i j, ‖u i j‖ ≤ diagonalTransportEnvelope c R S i j) →
      ∀ m n,
        ‖nonlinear u m n‖ ≤
          ((m + n).choose m : ℝ) * R ^ m * S ^ n * g (m + n))
    (hrec : ∀ m n,
      ((m + 1 : ℕ) : ℝ) • a (m + 1) n =
        (n : ℝ) • transport m n + nonlinear a m n) :
    ∀ m n, ‖a m n‖ ≤ diagonalTransportEnvelope c R S m n := by
  let nonlinear₀ : (ℕ → ℕ → (ι → ℝ)) → ℕ → ℕ → (ι → ℝ) :=
    fun u => nonlinear (zeroOrigin u)
  apply norm_le_diagonalTransportEnvelope_of_causal_vector_recurrence
    (a := a) (transport := transport) (nonlinear := nonlinear₀)
    hL hR hS hc hstep hzero htransport
  · intro u v m n huv
    apply hcausal
    intro i j hij
    unfold zeroOrigin
    split_ifs
    · rfl
    · exact huv i j hij
  · intro u hu
    apply hnonlinear (zeroOrigin u)
    · exact zeroOrigin_zero_zero u
    · intro i j
      by_cases hij : i = 0 ∧ j = 0
      · rcases hij with ⟨rfl, rfl⟩
        rw [zeroOrigin_zero_zero, norm_zero]
        unfold diagonalTransportEnvelope
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hR _))
            (pow_nonneg hS _))
          (hc 0)
      · simpa [zeroOrigin, hij] using hu i j
  · intro m n
    change ((m + 1 : ℕ) : ℝ) • a (m + 1) n =
      (n : ℝ) • transport m n + nonlinear (zeroOrigin a) m n
    rw [zeroOrigin_eq ha00]
    exact hrec m n

end
end CKStableTransportMajorant
end StressTensor
