import StressTensor.CKNagumoMajorant

/-!
# Closing the Fuchsian transport inequality with the Nagumo kernel

This file records the elementary uniform inequalities used to choose the
`x`-growth rate in the reduced Cauchy--Kowalevskaya recurrence.  The
constant source term is isolated at total degree zero; the remaining source
and derivative-product terms have the two stable Nagumo shapes appearing in
`CKNagumoMajorant`.
-/

namespace StressTensor
namespace CKNagumoTransportClosure

open CKNagumoMajorant

noncomputable section

theorem nagumoCoeff_le_one (k : ℕ) : nagumoCoeff k ≤ 1 := by
  unfold nagumoCoeff
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk : 1 ≤ (k + 1 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (k : ℝ)]
  exact (div_le_one (by positivity : 0 < (k + 1 : ℝ) ^ 2)).2 hk

/-- One unweighted Nagumo coefficient can be advanced by one degree with a
uniform factor four. -/
theorem nagumoCoeff_le_four_succ (k : ℕ) :
    nagumoCoeff k ≤
      4 * ((k + 1 : ℕ) : ℝ) * nagumoCoeff (k + 1) := by
  unfold nagumoCoeff
  have hk1 : 0 < (k + 1 : ℝ) := by positivity
  have hk2 : 0 < (k + 2 : ℝ) := by positivity
  have hk1one : 1 ≤ (k + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hsquare : (k + 2 : ℝ) ^ 2 ≤ 4 * (k + 1 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (k : ℝ)]
  have hcubic : (k + 2 : ℝ) ^ 2 ≤ 4 * (k + 1 : ℝ) ^ 3 := by
    calc
      (k + 2 : ℝ) ^ 2 ≤ 4 * (k + 1 : ℝ) ^ 2 := hsquare
      _ ≤ 4 * (k + 1 : ℝ) ^ 3 := by
        have hmul : (k + 1 : ℝ) ^ 2 ≤ (k + 1 : ℝ) ^ 3 := by
          have hpos : 0 < (k + 1 : ℝ) ^ 2 := sq_pos_of_pos hk1
          calc
            (k + 1 : ℝ) ^ 2 ≤ (k + 1 : ℝ) ^ 2 * (k + 1 : ℝ) :=
              (le_mul_iff_one_le_right hpos).2 hk1one
            _ = (k + 1 : ℝ) ^ 3 := by ring
        linarith
  field_simp
  convert hcubic using 1 <;> push_cast <;> ring

/-- A concrete positive evolution rate that dominates every contribution
in `nagumo_transport_step`. -/
def evolutionRate (L B C D epsilon : ℝ) : ℝ :=
  1 + (2 * L + 4 * C + D * epsilon + 4 * B / epsilon)

theorem evolutionRate_pos
    {L B C D epsilon : ℝ}
    (hL : 0 ≤ L) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hepsilon : 0 < epsilon) :
    0 < evolutionRate L B C D epsilon := by
  unfold evolutionRate
  have hdiv : 0 ≤ 4 * B / epsilon :=
    div_nonneg (mul_nonneg (by norm_num) hB) hepsilon.le
  positivity

theorem le_evolutionRate
    (L B C D epsilon : ℝ) :
    2 * L + 4 * C + D * epsilon + 4 * B / epsilon ≤
      evolutionRate L B C D epsilon := by
  unfold evolutionRate
  linarith

/-- The degree-zero point source is absorbed by the same advanced Nagumo
coefficient after choosing the evolution rate at least `4 * B / ε`. -/
theorem degreeZero_le_advanced_nagumo
    {ε B : ℝ} (hε : 0 < ε) (hB : 0 ≤ B) (k : ℕ) :
    (if k = 0 then B else 0) ≤
      (4 * B / ε) * (((k + 1 : ℕ) : ℝ) * ε * nagumoCoeff (k + 1)) := by
  by_cases hk : k = 0
  · subst k
    simp only [nagumoCoeff]
    norm_num
    have hε0 : ε ≠ 0 := ne_of_gt hε
    calc
      B = (4 * B / ε) * (ε * (1 / 4)) := by field_simp
      _ ≤ (4 * B / ε) * (ε * (1 / 4)) := le_rfl
  · simp only [hk, if_false]
    exact mul_nonneg
      (div_nonneg (mul_nonneg (by norm_num) hB) hε.le)
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) hε.le)
        (nagumoCoeff_nonneg _))

/-- A uniform scalar criterion that closes the total-degree transport step.

Here `B` bounds the isolated degree-zero source, `C * ε * φₖ` bounds
the positive-degree analytic source, and
`D * ε² * (k+1) * φₖ₊₁` bounds the differentiated nonlinear
product. -/
theorem nagumo_transport_step
    {ε L B C D R : ℝ} {g : ℕ → ℝ}
    (hε : 0 < ε) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hR : 2 * L + 4 * C + D * ε + 4 * B / ε ≤ R)
    (hg : ∀ k,
      g k ≤ (if k = 0 then B else 0) +
        C * ε * nagumoCoeff k +
        D * ε ^ 2 * ((k + 1 : ℕ) : ℝ) * nagumoCoeff (k + 1)) :
    ∀ k : ℕ,
      L * (k : ℝ) * (ε * nagumoCoeff k) + g k ≤
        ((k + 1 : ℕ) : ℝ) * R * (ε * nagumoCoeff (k + 1)) := by
  intro k
  let next : ℝ := ((k + 1 : ℕ) : ℝ) * ε * nagumoCoeff (k + 1)
  have hnext : 0 ≤ next := by
    dsimp [next]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) hε.le)
      (nagumoCoeff_nonneg _)
  have hlinear :
      L * (k : ℝ) * (ε * nagumoCoeff k) ≤ 2 * L * next := by
    have h : (k : ℝ) * nagumoCoeff k ≤
        2 * ((k + 1 : ℕ) : ℝ) * nagumoCoeff (k + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        nat_mul_nagumoCoeff_le_two_succ k
    dsimp [next]
    calc
      L * (k : ℝ) * (ε * nagumoCoeff k) =
          (L * ε) * ((k : ℝ) * nagumoCoeff k) := by ring
      _ ≤ (L * ε) *
          (2 * ((k + 1 : ℕ) : ℝ) * nagumoCoeff (k + 1)) :=
        mul_le_mul_of_nonneg_left h (mul_nonneg hL hε.le)
      _ = 2 * L * (((k + 1 : ℕ) : ℝ) * ε * nagumoCoeff (k + 1)) := by
        ring
  have hsource : C * ε * nagumoCoeff k ≤ 4 * C * next := by
    have h := nagumoCoeff_le_four_succ k
    dsimp [next]
    calc
      C * ε * nagumoCoeff k ≤
          (C * ε) *
            (4 * ((k + 1 : ℕ) : ℝ) * nagumoCoeff (k + 1)) :=
        mul_le_mul_of_nonneg_left h (mul_nonneg hC hε.le)
      _ = 4 * C * (((k + 1 : ℕ) : ℝ) * ε * nagumoCoeff (k + 1)) := by
        ring
  have hquadratic :
      D * ε ^ 2 * ((k + 1 : ℕ) : ℝ) * nagumoCoeff (k + 1) ≤
        (D * ε) * next := by
    dsimp [next]
    simp only [pow_two, Nat.cast_add, Nat.cast_one]
    ring_nf
    exact le_rfl
  have hzero := degreeZero_le_advanced_nagumo hε hB k
  have hg' : g k ≤
      (4 * B / ε) * next + 4 * C * next + (D * ε) * next := by
    calc
      g k ≤ (if k = 0 then B else 0) +
          C * ε * nagumoCoeff k +
          D * ε ^ 2 * ((k + 1 : ℕ) : ℝ) * nagumoCoeff (k + 1) := hg k
      _ ≤ (4 * B / ε) * next + 4 * C * next + (D * ε) * next := by
        linarith
  calc
    L * (k : ℝ) * (ε * nagumoCoeff k) + g k ≤
        (2 * L + 4 * C + D * ε + 4 * B / ε) * next := by
      calc
        L * (k : ℝ) * (ε * nagumoCoeff k) + g k ≤
            2 * L * next +
              ((4 * B / ε) * next + 4 * C * next + (D * ε) * next) :=
          add_le_add hlinear hg'
        _ = (2 * L + 4 * C + D * ε + 4 * B / ε) * next := by ring
    _ ≤ R * next := mul_le_mul_of_nonneg_right hR hnext
    _ = ((k + 1 : ℕ) : ℝ) * R * (ε * nagumoCoeff (k + 1)) := by
      dsimp [next]
      ring

end
end CKNagumoTransportClosure
end StressTensor
