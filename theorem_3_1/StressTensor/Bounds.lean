import StressTensor.Definitions

/-!
# Elementary bounds for the stress-tensor ansatz

This file formalizes the finite-dimensional estimates used to pass from the
jet domain `U_q` to the scalar domain `V_q`.  The analytic estimates for
`Ctilde` and `Stilde` are deliberately not assumed here.  The last two
theorems instead isolate exactly the scalar hypotheses on `S` and its
`d`-derivative which imply that the leading coefficient is nonzero.
-/

namespace StressTensor

noncomputable section

namespace Params

/-- The radius in (3.17) is strictly positive. -/
theorem rho_pos (P : Params) : 0 < P.rho := by
  rw [rho]
  exact div_pos (sub_pos.mpr P.one_lt_q) (mul_pos (by norm_num) P.q_pos)

/-- A convenient numerical upper bound for the radius in (3.17). -/
theorem rho_lt_one_div_1024 (P : Params) : P.rho < (1 : ℝ) / 1024 := by
  rw [rho]
  apply (div_lt_iff₀ (mul_pos (by norm_num) P.q_pos)).2
  norm_num
  linarith [P.one_lt_q]

theorem rho_lt_one (P : Params) : P.rho < 1 := by
  linarith [P.rho_lt_one_div_1024]

theorem rho_lt_one_half (P : Params) : P.rho < (1 : ℝ) / 2 := by
  linarith [P.rho_lt_one_div_1024]

end Params

namespace InU

variable {P : Params} {x y : ℝ} {z : Jet}

theorem abs_x_lt (h : InU P x y z) : |x| < P.rho := h.1.1

theorem abs_y_lt (h : InU P x y z) : |y| < P.rho := h.1.2

theorem abs_val_lt (h : InU P x y z) : |z.val| < P.rho := h.2.1

theorem abs_dx_add_one_lt (h : InU P x y z) : |z.dx + 1| < P.rho := h.2.2.1

theorem abs_dy_lt (h : InU P x y z) : |z.dy| < P.rho := h.2.2.2.1

theorem abs_dxy_lt (h : InU P x y z) : |z.dxy| < 1 := h.2.2.2.2.1

theorem abs_dyy_lt (h : InU P x y z) : |z.dyy| < 1 := h.2.2.2.2.2

/-- The `x`-derivative component lies in the interval centered at `-1`. -/
theorem dx_bounds (h : InU P x y z) :
    -1 - P.rho < z.dx ∧ z.dx < -1 + P.rho := by
  have hdx := (abs_lt.mp h.abs_dx_add_one_lt)
  constructor <;> linarith

/-- The paper's convenient consequence `|z₂| < 1 + ϱ_q`. -/
theorem abs_dx_lt_one_add_rho (h : InU P x y z) :
    |z.dx| < 1 + P.rho := by
  have hbounds := h.dx_bounds
  have hneg : z.dx < 0 := by
    linarith [P.rho_lt_one]
  rw [abs_of_neg hneg]
  linarith

end InU

/-- On `U_q`, the second auxiliary component has the bound used in (3.19). -/
theorem abs_gamma2_lt
    {P : Params} {x y : ℝ} {z : Jet} (h : InU P x y z) :
    |gamma2 y z| < P.rho * (1 + P.rho) := by
  have hrho : 0 < P.rho := P.rho_pos
  have hmul : |y| * |z.dy| < P.rho * P.rho :=
    mul_lt_mul'' h.abs_y_lt h.abs_dy_lt (abs_nonneg _) (abs_nonneg _)
  calc
    |gamma2 y z| = |z.val + y * z.dy / 2| := rfl
    _ ≤ |z.val| + |y * z.dy / 2| := abs_add_le _ _
    _ = |z.val| + |y| * |z.dy| / 2 := by
      rw [abs_div, abs_mul]
      norm_num
    _ < P.rho + (P.rho * P.rho) / 2 := by
      linarith [h.abs_val_lt]
    _ < P.rho * (1 + P.rho) := by
      nlinarith

/-- The algebraic triangle estimate underlying the `Γ₀` bound. -/
theorem abs_gamma0_add_two_le (y : ℝ) (z : Jet) :
    |gamma0 y z + 2| ≤
      2 * |z.dx + 1| + y ^ 2 * z.dx ^ 2 + 4 * gamma2 y z ^ 2 := by
  calc
    |gamma0 y z + 2| =
        |2 * (z.dx + 1) + (y ^ 2 * z.dx ^ 2 + 4 * gamma2 y z ^ 2)| := by
          simp only [gamma0]
          congr 1
          ring
    _ ≤ |2 * (z.dx + 1)| +
        |y ^ 2 * z.dx ^ 2 + 4 * gamma2 y z ^ 2| := abs_add_le _ _
    _ = 2 * |z.dx + 1| + y ^ 2 * z.dx ^ 2 + 4 * gamma2 y z ^ 2 := by
      have hnonneg : 0 ≤ y ^ 2 * z.dx ^ 2 + 4 * gamma2 y z ^ 2 := by
        positivity
      rw [abs_mul, abs_of_nonneg hnonneg]
      norm_num
      ring

/-- The explicit, pre-numerical estimate displayed after (3.17). -/
theorem abs_gamma0_add_two_lt_preliminary
    {P : Params} {x y : ℝ} {z : Jet} (h : InU P x y z) :
    |gamma0 y z + 2| <
      2 * P.rho + P.rho ^ 2 * (1 + P.rho) ^ 2 +
        4 * P.rho ^ 2 * (1 + P.rho) ^ 2 := by
  have hrho : 0 < P.rho := P.rho_pos
  have hy_sq : y ^ 2 < P.rho ^ 2 := by
    apply (sq_lt_sq).2
    simpa [abs_of_pos hrho] using h.abs_y_lt
  have hdx_sq : z.dx ^ 2 < (1 + P.rho) ^ 2 := by
    apply (sq_lt_sq).2
    have hone : 0 < 1 + P.rho := by positivity
    simpa [abs_of_pos hone] using h.abs_dx_lt_one_add_rho
  have hydx : y ^ 2 * z.dx ^ 2 < P.rho ^ 2 * (1 + P.rho) ^ 2 :=
    mul_lt_mul'' hy_sq hdx_sq (sq_nonneg _) (sq_nonneg _)
  have hgamma2_sq : gamma2 y z ^ 2 <
      (P.rho * (1 + P.rho)) ^ 2 := by
    apply (sq_lt_sq).2
    have hpos : 0 < P.rho * (1 + P.rho) := by positivity
    simpa [abs_of_pos hpos] using abs_gamma2_lt h
  have hgamma2_sq' : gamma2 y z ^ 2 <
      P.rho ^ 2 * (1 + P.rho) ^ 2 := by
    simpa [mul_pow] using hgamma2_sq
  calc
    |gamma0 y z + 2| ≤
        2 * |z.dx + 1| + y ^ 2 * z.dx ^ 2 + 4 * gamma2 y z ^ 2 :=
      abs_gamma0_add_two_le y z
    _ < 2 * P.rho + P.rho ^ 2 * (1 + P.rho) ^ 2 +
        4 * P.rho ^ 2 * (1 + P.rho) ^ 2 := by
      nlinarith [h.abs_dx_add_one_lt, hydx, hgamma2_sq']

/-- The numerical choice `ϱ_q = 2⁻¹⁰(q-1)/q` closes the `Γ₀` estimate. -/
theorem abs_gamma0_add_two_lt_four_rho
    {P : Params} {x y : ℝ} {z : Jet} (h : InU P x y z) :
    |gamma0 y z + 2| < 4 * P.rho := by
  have hrho : 0 < P.rho := P.rho_pos
  have hrho_one : P.rho < 1 := P.rho_lt_one
  have hsum : 1 + P.rho < 2 := by linarith
  have hsum_sq : (1 + P.rho) ^ 2 < (2 : ℝ) ^ 2 := by
    exact (sq_lt_sq₀ (by positivity) (by norm_num)).2 hsum
  norm_num at hsum_sq
  have hscaled : P.rho ^ 2 * (1 + P.rho) ^ 2 < P.rho ^ 2 * 4 := by
    exact mul_lt_mul_of_pos_left hsum_sq (sq_pos_of_pos hrho)
  have htwenty : 20 * P.rho < 2 := by
    linarith [P.rho_lt_one_div_1024]
  have hsmall : (20 * P.rho) * P.rho < 2 * P.rho :=
    mul_lt_mul_of_pos_right htwenty hrho
  have htail :
      5 * P.rho ^ 2 * (1 + P.rho) ^ 2 < 2 * P.rho := by
    calc
      5 * P.rho ^ 2 * (1 + P.rho) ^ 2 < 5 * (P.rho ^ 2 * 4) := by
        nlinarith [hscaled]
      _ = (20 * P.rho) * P.rho := by ring
      _ < 2 * P.rho := hsmall
  have hpre := abs_gamma0_add_two_lt_preliminary h
  nlinarith

/-- The domain inclusion `(x,y,z) ∈ U_q ⇒ (y,Γ₀) ∈ V_q`. -/
theorem inV_gamma0_of_inU
    {P : Params} {x y : ℝ} {z : Jet} (h : InU P x y z) :
    InV P y (gamma0 y z) :=
  ⟨h.abs_y_lt, abs_gamma0_add_two_lt_four_rho h⟩

/-- The perturbation of `Γ₁` from one is quadratically small in `ϱ_q`. -/
theorem abs_gamma1_sub_one_lt
    {P : Params} {x y : ℝ} {z : Jet} (h : InU P x y z) :
    |gamma1 y z - 1| < P.rho ^ 2 * (1 + P.rho) := by
  have hrho : 0 < P.rho := P.rho_pos
  have hy_sq : y ^ 2 < P.rho ^ 2 := by
    apply (sq_lt_sq).2
    simpa [abs_of_pos hrho] using h.abs_y_lt
  have hprod : y ^ 2 * |z.dx| < P.rho ^ 2 * (1 + P.rho) :=
    mul_lt_mul'' hy_sq h.abs_dx_lt_one_add_rho (sq_nonneg _) (abs_nonneg _)
  rw [gamma1]
  have hsquare : |y ^ 2| = y ^ 2 := abs_of_nonneg (sq_nonneg _)
  simpa [abs_mul, hsquare] using hprod

/-- The elementary lower bound for `Γ₁` asserted after (3.20). -/
theorem gamma1_ge_one_half
    {P : Params} {x y : ℝ} {z : Jet} (h : InU P x y z) :
    (1 : ℝ) / 2 ≤ gamma1 y z := by
  have hrho : 0 < P.rho := P.rho_pos
  have hsum : 1 + P.rho < 2 := by linarith [P.rho_lt_one]
  have hrho_sq_lt : P.rho ^ 2 < P.rho := by
    nlinarith [P.rho_lt_one]
  have hsmall : P.rho ^ 2 * (1 + P.rho) < (1 : ℝ) / 2 := by
    have hscaled := mul_lt_mul'' hrho_sq_lt hsum (sq_nonneg _) (by positivity)
    have htwo_rho : 2 * P.rho < (1 : ℝ) / 2 := by
      linarith [P.rho_lt_one_div_1024]
    nlinarith
  have hperturb := abs_gamma1_sub_one_lt h
  have hlower := (abs_lt.mp (lt_trans hperturb hsmall)).1
  linarith

namespace InV

variable {P : Params} {t d : ℝ}

/-- On `V_q`, the scalar variable remains in the interval used in (3.19). -/
theorem neg_d_bounds (h : InV P t d) : 1 < -d ∧ -d < 4 := by
  have hd := abs_lt.mp h.2
  have hrho := P.rho_lt_one_div_1024
  constructor <;> linarith

/-- The product `t²d` is uniformly small on `V_q`. -/
theorem abs_t_sq_mul_d_lt (h : InV P t d) :
    |t ^ 2 * d| < 4 * P.rho ^ 2 := by
  have hd_abs : |d| < 4 := by
    have hd := h.neg_d_bounds
    have hd_interval : -4 < d ∧ d < 4 := by constructor <;> linarith
    exact abs_lt.mpr hd_interval
  have ht_sq : t ^ 2 < P.rho ^ 2 := by
    apply (sq_lt_sq).2
    simpa [abs_of_pos P.rho_pos] using h.1
  have hprod : t ^ 2 * |d| < P.rho ^ 2 * 4 :=
    mul_lt_mul'' ht_sq hd_abs (sq_nonneg _) (abs_nonneg _)
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  nlinarith

end InV

/--
A modular version of the lower bound for `c₀`: the logarithmic derivative
estimate is supplied without division as `S (q-1)/32 ≤ ∂_d S`.
-/
theorem coeff0_ge_q_sub_one_div_1024
    (P : Params) (y : ℝ) (z : Jet) (a : ScalarData)
    (hS : (1 : ℝ) / 8 ≤ a.S)
    (hderiv : a.S * ((P.q - 1) / 32) ≤ a.dSdd)
    (hgamma1 : (1 : ℝ) / 2 ≤ gamma1 y z) :
    (P.q - 1) / 1024 ≤ coeff0 y z a := by
  have hqsub : 0 < P.q - 1 := sub_pos.mpr P.one_lt_q
  have hS0 : 0 ≤ a.S := by linarith
  have hfactor0 : 0 ≤ (P.q - 1) / 32 := by positivity
  have hd_lower : (P.q - 1) / 256 ≤ a.dSdd := by
    calc
      (P.q - 1) / 256 = ((1 : ℝ) / 8) * ((P.q - 1) / 32) := by ring
      _ ≤ a.S * ((P.q - 1) / 32) :=
        mul_le_mul_of_nonneg_right hS hfactor0
      _ ≤ a.dSdd := hderiv
  have hd0 : 0 ≤ a.dSdd := by
    have : 0 < (P.q - 1) / 256 := by positivity
    exact le_trans (le_of_lt this) hd_lower
  have hgamma_sq : (1 : ℝ) / 4 ≤ gamma1 y z ^ 2 := by
    nlinarith [sq_nonneg (gamma1 y z - (1 : ℝ) / 2)]
  have hprod : ((1 : ℝ) / 4) * ((P.q - 1) / 256) ≤
      gamma1 y z ^ 2 * a.dSdd :=
    mul_le_mul hgamma_sq hd_lower (by positivity) (sq_nonneg _)
  rw [coeff0]
  nlinarith [mul_nonneg (sq_nonneg y) hS0]

/-- The same `c₀` estimate in the ratio form appearing in (3.20). -/
theorem coeff0_ge_q_sub_one_div_1024_of_ratio
    (P : Params) (y : ℝ) (z : Jet) (a : ScalarData)
    (hS : (1 : ℝ) / 8 ≤ a.S)
    (hratio : (P.q - 1) / 32 ≤ a.dSdd / a.S)
    (hgamma1 : (1 : ℝ) / 2 ≤ gamma1 y z) :
    (P.q - 1) / 1024 ≤ coeff0 y z a := by
  have hSpos : 0 < a.S := by linarith
  apply coeff0_ge_q_sub_one_div_1024 P y z a hS
  · have hmul := (le_div_iff₀ hSpos).mp hratio
    simpa [mul_comm] using hmul
  · exact hgamma1

/-- Fully finite-dimensional form of the `c₀` lower bound on `U_q`. -/
theorem coeff0_ge_q_sub_one_div_1024_of_inU
    (P : Params) {x y : ℝ} {z : Jet} (a : ScalarData)
    (hU : InU P x y z)
    (hS : (1 : ℝ) / 8 ≤ a.S)
    (hderiv : a.S * ((P.q - 1) / 32) ≤ a.dSdd) :
    (P.q - 1) / 1024 ≤ coeff0 y z a :=
  coeff0_ge_q_sub_one_div_1024 P y z a hS hderiv (gamma1_ge_one_half hU)

end

end StressTensor
