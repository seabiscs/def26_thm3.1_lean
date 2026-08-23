import StressTensor.NormalFormAnalyticity

/-!
# Quasilinear structure of the shifted CK equation

The Cauchy data are `gamma(0,y) = 0` and `gamma_x(0,y) = -1`.
It is therefore useful to remove their affine part by writing

`h(x,y) = gamma(x,y) + x`.

Then `h` has zero Cauchy data.  This file records the further special
structure of the normal form which is useful for a coefficient-majorant
proof of Cauchy--Kowalevskaya: it is affine in `gamma_xy` and `gamma_yy`.
After the shift, the coefficient of `h_xy` has the exact factor
`y * Gamma₂`, while the coefficient of `h_yy` has the exact factor `y²`.

These are algebraic statements only.  In particular, this file does not
assert convergence of the formal CK recursion.
-/

namespace StressTensor

noncomputable section

/-! ## The affine principal-part decomposition -/

/-- Coefficient of the mixed derivative in the normal form. -/
def quasilinearCoeffXY (y : ℝ) (z : Jet) (a : ScalarData) : ℝ :=
  -(2 * coeff1 y z a) / coeff0 y z a

/-- Coefficient of the pure tangential second derivative in the normal form. -/
def quasilinearCoeffYY (y : ℝ) (z : Jet) (a : ScalarData) : ℝ :=
  -(coeff2 y z a) / coeff0 y z a

/-- The part of the normal form which contains no second derivative. -/
def quasilinearConstant (P : Params) (y : ℝ) (z : Jet) (a : ScalarData) : ℝ :=
  -(lowerOrder P y z a) / coeff0 y z a

/-- The CK normal form is affine in the two highest tangential derivatives.
This identity remains true even when the displayed denominator is zero,
because both sides use the same totalized field division. -/
theorem normalForm_eq_quasilinear
    (P : Params) (y : ℝ) (z : Jet) (a : ScalarData) :
    normalForm P y z a =
      quasilinearCoeffXY y z a * z.dxy +
        quasilinearCoeffYY y z a * z.dyy +
          quasilinearConstant P y z a := by
  simp only [normalForm, quasilinearCoeffXY, quasilinearCoeffYY,
    quasilinearConstant]
  ring

/-! ## Zero-Cauchy-data coordinates -/

/-- The five low-order coordinates `(x,y,h,h_x,h_y)` after setting
`h = gamma + x`. -/
abbrev ShiftedPhase := Fin 5 → ℝ

/-- Recover the `gamma` jet from the shifted variables and the two highest
derivatives.  Since `gamma = h - x`, its `x` derivative is `h_x - 1` and all
other displayed derivatives agree with those of `h`. -/
def shiftedJet (v : ShiftedPhase) (hxy hyy : ℝ) : Jet where
  val := v 2 - v 0
  dx := v 3 - 1
  dy := v 4
  dxy := hxy
  dyy := hyy

/-- A representative shifted jet with the two affine derivative coordinates
set to zero.  All coefficients below are independent of these two fields. -/
def shiftedLowJet (v : ShiftedPhase) : Jet :=
  shiftedJet v 0 0

/-- The shifted form of `Gamma₂`. -/
def shiftedGamma2 (v : ShiftedPhase) : ℝ :=
  v 2 - v 0 + v 1 * v 4 / 2

@[simp] theorem gamma1_shiftedJet (v : ShiftedPhase) (hxy hyy : ℝ) :
    gamma1 (v 1) (shiftedJet v hxy hyy) =
      1 + (v 1) ^ 2 * (v 3 - 1) := by
  rfl

@[simp] theorem gamma2_shiftedJet (v : ShiftedPhase) (hxy hyy : ℝ) :
    gamma2 (v 1) (shiftedJet v hxy hyy) = shiftedGamma2 v := by
  rfl

@[simp] theorem gamma0_shiftedJet_independent
    (v : ShiftedPhase) (hxy hyy : ℝ) :
    gamma0 (v 1) (shiftedJet v hxy hyy) =
      gamma0 (v 1) (shiftedLowJet v) := by
  rfl

/-- Scalar data in shifted low-order coordinates. -/
def shiftedScalarData (P : Params) (v : ShiftedPhase) : ScalarData :=
  scalarDataOfJet P (v 1) (shiftedLowJet v)

/-- The shifted low-order phase lies in the manuscript's CK neighborhood. -/
def ShiftedPhaseInU (P : Params) (v : ShiftedPhase) : Prop :=
  InU P (v 0) (v 1) (shiftedLowJet v)

@[simp] theorem scalarDataOfJet_shiftedJet
    (P : Params) (v : ShiftedPhase) (hxy hyy : ℝ) :
    scalarDataOfJet P (v 1) (shiftedJet v hxy hyy) =
      shiftedScalarData P v := by
  rfl

/-- The complete seven-coordinate CK phase associated to the shift. -/
def shiftedCKPhase (v : ShiftedPhase) (hxy hyy : ℝ) : CKPhase :=
  fun i =>
    match i with
    | 0 => v 0
    | 1 => v 1
    | 2 => v 2 - v 0
    | 3 => v 3 - 1
    | 4 => v 4
    | 5 => hxy
    | 6 => hyy

@[simp] theorem ckPhaseJet_shiftedCKPhase
    (v : ShiftedPhase) (hxy hyy : ℝ) :
    ckPhaseJet (shiftedCKPhase v hxy hyy) = shiftedJet v hxy hyy := by
  rfl

@[simp] theorem ckNormalForm_shiftedCKPhase
    (P : Params) (v : ShiftedPhase) (hxy hyy : ℝ) :
    ckNormalForm P (shiftedCKPhase v hxy hyy) =
      normalForm P (v 1) (shiftedJet v hxy hyy)
        (shiftedScalarData P v) := by
  rfl

@[simp] theorem ckPhaseInU_shiftedCKPhase_zero
    (P : Params) (v : ShiftedPhase) :
    CKPhaseInU P (shiftedCKPhase v 0 0) ↔ ShiftedPhaseInU P v := by
  rfl

/-- The affine passage from zero-data coordinates to the seven-dimensional
CK phase is analytic. -/
theorem analyticAt_shiftedCKPhase_zero (v : ShiftedPhase) :
    AnalyticAt ℝ (fun w : ShiftedPhase => shiftedCKPhase w 0 0) v := by
  have hc (i : Fin 5) : AnalyticAt ℝ (fun w : ShiftedPhase => w i) v :=
    (ContinuousLinearMap.proj (R := ℝ) i).analyticAt v
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · simpa only [shiftedCKPhase] using hc 0
  · simpa only [shiftedCKPhase] using hc 1
  · have h := (hc 2).sub (hc 0)
    convert! h using 1
  · have h := (hc 3).sub
      (analyticAt_const : AnalyticAt ℝ (fun _ : ShiftedPhase => (1 : ℝ)) v)
    convert! h using 1
  · simpa only [shiftedCKPhase] using hc 4
  · simpa only [shiftedCKPhase] using
      (analyticAt_const : AnalyticAt ℝ (fun _ : ShiftedPhase => (0 : ℝ)) v)
  · simpa only [shiftedCKPhase] using
      (analyticAt_const : AnalyticAt ℝ (fun _ : ShiftedPhase => (0 : ℝ)) v)

/-! ## Exact vanishing factors of the principal coefficients -/

/-- The mixed-derivative coefficient after the zero-data shift. -/
def shiftedCoeffXY (P : Params) (v : ShiftedPhase) : ℝ :=
  quasilinearCoeffXY (v 1) (shiftedLowJet v) (shiftedScalarData P v)

/-- The pure tangential coefficient after the zero-data shift. -/
def shiftedCoeffYY (P : Params) (v : ShiftedPhase) : ℝ :=
  quasilinearCoeffYY (v 1) (shiftedLowJet v) (shiftedScalarData P v)

/-- The lower-order term after the zero-data shift. -/
def shiftedConstant (P : Params) (v : ShiftedPhase) : ℝ :=
  quasilinearConstant P (v 1) (shiftedLowJet v) (shiftedScalarData P v)

/-- The analytic quotient left after extracting `y * Gamma₂` from the
mixed-derivative coefficient. -/
def shiftedCoeffXYFactor (P : Params) (v : ShiftedPhase) : ℝ :=
  -(8 * gamma1 (v 1) (shiftedLowJet v) *
      (shiftedScalarData P v).dSdd) /
    coeff0 (v 1) (shiftedLowJet v) (shiftedScalarData P v)

/-- The analytic quotient left after extracting `y²` from the pure
tangential coefficient. -/
def shiftedCoeffYYFactor (P : Params) (v : ShiftedPhase) : ℝ :=
  -((shiftedScalarData P v).S +
      8 * shiftedGamma2 v ^ 2 * (shiftedScalarData P v).dSdd) /
    coeff0 (v 1) (shiftedLowJet v) (shiftedScalarData P v)

/-! ## Analyticity of the extracted coefficients -/

private theorem shiftedAnalyticAt_add
    {f g : ShiftedPhase → ℝ} {v : ShiftedPhase}
    (hf : AnalyticAt ℝ f v) (hg : AnalyticAt ℝ g v) :
    AnalyticAt ℝ (fun w => f w + g w) v := by
  convert! hf.add hg using 1

private theorem shiftedAnalyticAt_mul
    {f g : ShiftedPhase → ℝ} {v : ShiftedPhase}
    (hf : AnalyticAt ℝ f v) (hg : AnalyticAt ℝ g v) :
    AnalyticAt ℝ (fun w => f w * g w) v := by
  convert! hf.mul hg using 1

private theorem shiftedAnalyticAt_pow
    {f : ShiftedPhase → ℝ} {v : ShiftedPhase}
    (hf : AnalyticAt ℝ f v) (n : ℕ) :
    AnalyticAt ℝ (fun w => f w ^ n) v := by
  convert! hf.pow n using 1

private theorem shiftedAnalyticAt_div_const
    {f : ShiftedPhase → ℝ} {v : ShiftedPhase} (c : ℝ)
    (hf : AnalyticAt ℝ f v) :
    AnalyticAt ℝ (fun w => f w / c) v := by
  convert! hf.div_const (c := c) using 1

private theorem shiftedAnalyticAt_const_mul
    {f : ShiftedPhase → ℝ} {v : ShiftedPhase} (c : ℝ)
    (hf : AnalyticAt ℝ f v) :
    AnalyticAt ℝ (fun w => c * f w) v := by
  exact shiftedAnalyticAt_mul analyticAt_const hf

private theorem shiftedAnalyticAt_neg
    {f : ShiftedPhase → ℝ} {v : ShiftedPhase}
    (hf : AnalyticAt ℝ f v) :
    AnalyticAt ℝ (fun w => -f w) v := by
  convert! hf.neg using 1

private theorem shiftedAnalyticAt_div
    {f g : ShiftedPhase → ℝ} {v : ShiftedPhase}
    (hf : AnalyticAt ℝ f v) (hg : AnalyticAt ℝ g v) (hg0 : g v ≠ 0) :
    AnalyticAt ℝ (fun w => f w / g w) v := by
  convert! hf.div hg hg0 using 1

/-- The three scalar-data coordinates remain analytic after the affine
zero-data shift. -/
theorem analyticAt_shiftedScalarData
    {P : Params} {v : ShiftedPhase} (hU : ShiftedPhaseInU P v) :
    AnalyticAt ℝ (fun w : ShiftedPhase => (shiftedScalarData P w).S) v ∧
      AnalyticAt ℝ (fun w : ShiftedPhase => (shiftedScalarData P w).dSdt) v ∧
      AnalyticAt ℝ (fun w : ShiftedPhase => (shiftedScalarData P w).dSdd) v := by
  let e : ShiftedPhase → CKPhase := fun w => shiftedCKPhase w 0 0
  have he : AnalyticAt ℝ e v := analyticAt_shiftedCKPhase_zero v
  have hphase : CKPhaseInU P (e v) := by
    simpa [e] using hU
  have hdata := analyticAt_ckScalarData hphase
  constructor
  · have h := hdata.1.comp he
    apply h.congr
    exact Filter.Eventually.of_forall fun w => by
      simp [Function.comp_apply, e, shiftedCKPhase, shiftedScalarData,
        scalarDataOfJet, shiftedLowJet]
  constructor
  · have h := hdata.2.1.comp he
    apply h.congr
    exact Filter.Eventually.of_forall fun w => by
      simp [Function.comp_apply, e, shiftedCKPhase, shiftedScalarData,
        scalarDataOfJet, shiftedLowJet]
  · have h := hdata.2.2.comp he
    apply h.congr
    exact Filter.Eventually.of_forall fun w => by
      simp [Function.comp_apply, e, shiftedCKPhase, shiftedScalarData,
        scalarDataOfJet, shiftedLowJet]

/-- The shifted leading coefficient is analytic throughout the shifted CK
neighborhood. -/
theorem analyticAt_shiftedCoeff0
    {P : Params} {v : ShiftedPhase} (hU : ShiftedPhaseInU P v) :
    AnalyticAt ℝ
      (fun w : ShiftedPhase =>
        coeff0 (w 1) (shiftedLowJet w) (shiftedScalarData P w)) v := by
  let e : ShiftedPhase → CKPhase := fun w => shiftedCKPhase w 0 0
  have he : AnalyticAt ℝ e v := analyticAt_shiftedCKPhase_zero v
  have hphase : CKPhaseInU P (e v) := by
    simpa [e] using hU
  have h := (analyticAt_ckCoeff0 hphase).comp he
  apply h.congr
  exact Filter.Eventually.of_forall fun w => by
    simp [Function.comp_apply, e, shiftedCKPhase, shiftedScalarData,
      scalarDataOfJet, shiftedLowJet]

/-- The quotient left after extracting `y * Gamma₂` is analytic wherever
the leading coefficient is nonzero; `ShiftedPhaseInU` supplies this
noncharacteristic fact automatically. -/
theorem analyticAt_shiftedCoeffXYFactor
    {P : Params} {v : ShiftedPhase} (hU : ShiftedPhaseInU P v) :
    AnalyticAt ℝ (shiftedCoeffXYFactor P) v := by
  have hy : AnalyticAt ℝ (fun w : ShiftedPhase => w 1) v :=
    (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 5)).analyticAt v
  have hdx : AnalyticAt ℝ (fun w : ShiftedPhase => w 3) v :=
    (ContinuousLinearMap.proj (R := ℝ) (3 : Fin 5)).analyticAt v
  have hgamma1 : AnalyticAt ℝ
      (fun w : ShiftedPhase => gamma1 (w 1) (shiftedLowJet w)) v := by
    have hone : AnalyticAt ℝ (fun _ : ShiftedPhase => (1 : ℝ)) v :=
      analyticAt_const
    have hsub : AnalyticAt ℝ (fun w : ShiftedPhase => w 3 - 1) v := by
      convert! hdx.sub hone using 1
    have hraw : AnalyticAt ℝ
        (fun w : ShiftedPhase => 1 + w 1 ^ 2 * (w 3 - 1)) v :=
      shiftedAnalyticAt_add hone
        (shiftedAnalyticAt_mul (shiftedAnalyticAt_pow hy 2) hsub)
    simpa only [gamma1, shiftedLowJet, shiftedJet] using hraw
  have hD := (analyticAt_shiftedScalarData hU).2.2
  have hden := analyticAt_shiftedCoeff0 hU
  have hden0 :
      coeff0 (v 1) (shiftedLowJet v) (shiftedScalarData P v) ≠ 0 := by
    exact (coeff0_scalarDataOfJet_pos_of_inU P hU).ne'
  have hnum : AnalyticAt ℝ
      (fun w : ShiftedPhase =>
        8 * gamma1 (w 1) (shiftedLowJet w) *
          (shiftedScalarData P w).dSdd) v := by
    exact shiftedAnalyticAt_mul
      (shiftedAnalyticAt_const_mul 8 hgamma1) hD
  have hnegnum : AnalyticAt ℝ
      (fun w : ShiftedPhase =>
        -(8 * gamma1 (w 1) (shiftedLowJet w) *
          (shiftedScalarData P w).dSdd)) v := by
    exact shiftedAnalyticAt_neg hnum
  have hquot := shiftedAnalyticAt_div hnegnum hden hden0
  apply hquot.congr
  exact Filter.Eventually.of_forall fun w => by
    simp only [shiftedCoeffXYFactor]

/-- The quotient left after extracting `y²` is analytic on the same shifted
CK neighborhood. -/
theorem analyticAt_shiftedCoeffYYFactor
    {P : Params} {v : ShiftedPhase} (hU : ShiftedPhaseInU P v) :
    AnalyticAt ℝ (shiftedCoeffYYFactor P) v := by
  have hx : AnalyticAt ℝ (fun w : ShiftedPhase => w 0) v :=
    (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 5)).analyticAt v
  have hy : AnalyticAt ℝ (fun w : ShiftedPhase => w 1) v :=
    (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 5)).analyticAt v
  have hval : AnalyticAt ℝ (fun w : ShiftedPhase => w 2) v :=
    (ContinuousLinearMap.proj (R := ℝ) (2 : Fin 5)).analyticAt v
  have hdy : AnalyticAt ℝ (fun w : ShiftedPhase => w 4) v :=
    (ContinuousLinearMap.proj (R := ℝ) (4 : Fin 5)).analyticAt v
  have hgamma2 : AnalyticAt ℝ shiftedGamma2 v := by
    have hsub : AnalyticAt ℝ (fun w : ShiftedPhase => w 2 - w 0) v := by
      convert! hval.sub hx using 1
    have hquot : AnalyticAt ℝ
        (fun w : ShiftedPhase => w 1 * w 4 / 2) v :=
      shiftedAnalyticAt_div_const 2 (shiftedAnalyticAt_mul hy hdy)
    have hraw : AnalyticAt ℝ
        (fun w : ShiftedPhase => (w 2 - w 0) + w 1 * w 4 / 2) v :=
      shiftedAnalyticAt_add hsub hquot
    apply hraw.congr
    exact Filter.Eventually.of_forall fun w => rfl
  have hS := (analyticAt_shiftedScalarData hU).1
  have hD := (analyticAt_shiftedScalarData hU).2.2
  have hinner : AnalyticAt ℝ
      (fun w : ShiftedPhase => (shiftedScalarData P w).S +
        8 * shiftedGamma2 w ^ 2 * (shiftedScalarData P w).dSdd) v := by
    exact shiftedAnalyticAt_add hS
      (shiftedAnalyticAt_mul
        (shiftedAnalyticAt_const_mul 8 (shiftedAnalyticAt_pow hgamma2 2)) hD)
  have hden := analyticAt_shiftedCoeff0 hU
  have hden0 :
      coeff0 (v 1) (shiftedLowJet v) (shiftedScalarData P v) ≠ 0 := by
    exact (coeff0_scalarDataOfJet_pos_of_inU P hU).ne'
  have hneginner : AnalyticAt ℝ
      (fun w : ShiftedPhase => -((shiftedScalarData P w).S +
        8 * shiftedGamma2 w ^ 2 * (shiftedScalarData P w).dSdd)) v := by
    exact shiftedAnalyticAt_neg hinner
  have hquot := shiftedAnalyticAt_div hneginner hden hden0
  apply hquot.congr
  exact Filter.Eventually.of_forall fun w => by
    simp only [shiftedCoeffYYFactor]

/-- Exact factorization of the mixed-derivative coefficient.  Both displayed
factors `y` and `shiftedGamma2` vanish at the shifted origin. -/
theorem shiftedCoeffXY_factorization (P : Params) (v : ShiftedPhase) :
    shiftedCoeffXY P v =
      v 1 * shiftedGamma2 v * shiftedCoeffXYFactor P v := by
  simp only [shiftedCoeffXY, quasilinearCoeffXY, coeff1,
    shiftedCoeffXYFactor]
  change -(2 * (4 * v 1 * gamma1 (v 1) (shiftedLowJet v) *
      shiftedGamma2 v * (shiftedScalarData P v).dSdd)) /
      coeff0 (v 1) (shiftedLowJet v) (shiftedScalarData P v) = _
  ring

/-- Exact factorization of the pure tangential coefficient by `y²`. -/
theorem shiftedCoeffYY_factorization (P : Params) (v : ShiftedPhase) :
    shiftedCoeffYY P v = (v 1) ^ 2 * shiftedCoeffYYFactor P v := by
  simp only [shiftedCoeffYY, quasilinearCoeffYY, coeff2,
    shiftedCoeffYYFactor]
  change -(v 1 ^ 2 * ((shiftedScalarData P v).S +
      8 * shiftedGamma2 v ^ 2 * (shiftedScalarData P v).dSdd)) /
      coeff0 (v 1) (shiftedLowJet v) (shiftedScalarData P v) = _
  ring

/-- In shifted coordinates the whole normal form has the promised
quasilinear decomposition. -/
theorem shifted_normalForm_eq
    (P : Params) (v : ShiftedPhase) (hxy hyy : ℝ) :
    normalForm P (v 1) (shiftedJet v hxy hyy)
        (shiftedScalarData P v) =
      shiftedCoeffXY P v * hxy + shiftedCoeffYY P v * hyy +
        shiftedConstant P v := by
  rw [normalForm_eq_quasilinear]
  rfl

/-- The derivative-free term is analytic after the zero-data shift. -/
theorem analyticAt_shiftedConstant
    {P : Params} {v : ShiftedPhase} (hU : ShiftedPhaseInU P v) :
    AnalyticAt ℝ (shiftedConstant P) v := by
  let e : ShiftedPhase → CKPhase := fun w => shiftedCKPhase w 0 0
  have he : AnalyticAt ℝ e v := analyticAt_shiftedCKPhase_zero v
  have hphase : CKPhaseInU P (e v) := by
    simpa [e] using hU
  have hG := (analyticAt_ckNormalForm hphase).comp he
  apply hG.congr
  exact Filter.Eventually.of_forall fun w => by
    change ckNormalForm P (shiftedCKPhase w 0 0) = shiftedConstant P w
    rw [ckNormalForm_shiftedCKPhase, shifted_normalForm_eq]
    ring

/-- The shifted origin. -/
def shiftedOrigin : ShiftedPhase := fun _ => 0

@[simp] theorem shiftedLowJet_origin : shiftedLowJet shiftedOrigin = initialJet := by
  simp [shiftedLowJet, shiftedJet, shiftedOrigin, initialJet]

@[simp] theorem shiftedGamma2_origin : shiftedGamma2 shiftedOrigin = 0 := by
  norm_num [shiftedGamma2, shiftedOrigin]

@[simp] theorem shiftedCoeffXY_origin (P : Params) :
    shiftedCoeffXY P shiftedOrigin = 0 := by
  rw [shiftedCoeffXY_factorization]
  norm_num [shiftedOrigin]

@[simp] theorem shiftedCoeffYY_origin (P : Params) :
    shiftedCoeffYY P shiftedOrigin = 0 := by
  rw [shiftedCoeffYY_factorization]
  norm_num [shiftedOrigin]

@[simp] theorem shiftedConstant_origin (P : Params) :
    shiftedConstant P shiftedOrigin = 0 := by
  simp [shiftedConstant, quasilinearConstant, shiftedOrigin, shiftedScalarData,
    scalarDataOfJet, shiftedLowJet, shiftedJet, lowerOrder, gamma1, gamma2]

/-- The mixed coefficient vanishes on `y = 0`. -/
theorem shiftedCoeffXY_eq_zero_of_y_eq_zero
    (P : Params) {v : ShiftedPhase} (hy : v 1 = 0) :
    shiftedCoeffXY P v = 0 := by
  rw [shiftedCoeffXY_factorization, hy]
  simp

/-- The mixed coefficient also vanishes on the shifted `Gamma₂ = 0` locus. -/
theorem shiftedCoeffXY_eq_zero_of_gamma2_eq_zero
    (P : Params) {v : ShiftedPhase} (hgamma2 : shiftedGamma2 v = 0) :
    shiftedCoeffXY P v = 0 := by
  rw [shiftedCoeffXY_factorization, hgamma2]
  simp

/-- The pure tangential coefficient vanishes on `y = 0`. -/
theorem shiftedCoeffYY_eq_zero_of_y_eq_zero
    (P : Params) {v : ShiftedPhase} (hy : v 1 = 0) :
    shiftedCoeffYY P v = 0 := by
  rw [shiftedCoeffYY_factorization, hy]
  simp

end

end StressTensor
