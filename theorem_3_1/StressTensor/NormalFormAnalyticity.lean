import StressTensor.AnalyticDifferentialBridge
import StressTensor.LocalizationBridge

/-!
# Finite-dimensional analyticity of the CK normal form

The manuscript applies Cauchy--Kowalevskaya to a function of the seven
coordinates `(x,y,γ,γₓ,γᵧ,γₓᵧ,γᵧᵧ)`.  This file gives those
coordinates the standard finite-dimensional normed-space structure and proves
that the resulting normal-form right-hand side is analytic at every point of
`U_q`.  In particular, the analyticity claim used immediately before (3.23)
is no longer an interface assumption.
-/

namespace StressTensor

noncomputable section

/-- The seven finite-dimensional variables `(x,y,z₁,…,z₅)` used in the
normal-form Cauchy problem. -/
abbrev CKPhase := Fin 7 → ℝ

/-- Recover the five-jet from its coordinates in `CKPhase`. -/
def ckPhaseJet (v : CKPhase) : Jet where
  val := v 2
  dx := v 3
  dy := v 4
  dxy := v 5
  dyy := v 6

/-- Membership in the manuscript's seven-dimensional set `U_q`. -/
def CKPhaseInU (P : Params) (v : CKPhase) : Prop :=
  InU P (v 0) (v 1) (ckPhaseJet v)

/-- The scalar point `(y,Γ₀)` attached to a phase point. -/
def ckScalarPoint (v : CKPhase) : ℝ × ℝ :=
  (v 1, gamma0 (v 1) (ckPhaseJet v))

/-- The normal-form right-hand side as an honest function on a normed
seven-dimensional real vector space. -/
def ckNormalForm (P : Params) (v : CKPhase) : ℝ :=
  normalForm P (v 1) (ckPhaseJet v)
    (scalarDataAt P (v 1) (gamma0 (v 1) (ckPhaseJet v)))

/-- Every coordinate projection on `CKPhase` is analytic. -/
theorem analyticAt_ckPhase_coord (i : Fin 7) (v : CKPhase) :
    AnalyticAt ℝ (fun w : CKPhase => w i) v :=
  (ContinuousLinearMap.proj (R := ℝ) i).analyticAt v

/-- Multiplication of a real-valued analytic function by an explicit real
constant, stated in pointwise notation. -/
private theorem ckAnalyticAt_add
    {f g : CKPhase → ℝ} {v : CKPhase}
    (hf : AnalyticAt ℝ f v) (hg : AnalyticAt ℝ g v) :
    AnalyticAt ℝ (fun w => f w + g w) v := by
  convert! hf.add hg using 1

private theorem ckAnalyticAt_mul
    {f g : CKPhase → ℝ} {v : CKPhase}
    (hf : AnalyticAt ℝ f v) (hg : AnalyticAt ℝ g v) :
    AnalyticAt ℝ (fun w => f w * g w) v := by
  convert! hf.mul hg using 1

private theorem ckAnalyticAt_pow
    {f : CKPhase → ℝ} {v : CKPhase}
    (hf : AnalyticAt ℝ f v) (n : ℕ) :
    AnalyticAt ℝ (fun w => f w ^ n) v := by
  convert! hf.pow n using 1

private theorem ckAnalyticAt_div_const
    {f : CKPhase → ℝ} {v : CKPhase} (c : ℝ)
    (hf : AnalyticAt ℝ f v) :
    AnalyticAt ℝ (fun w => f w / c) v := by
  convert! hf.div_const (c := c) using 1

private theorem ckAnalyticAt_const_mul
    {f : CKPhase → ℝ} {v : CKPhase} (c : ℝ)
    (hf : AnalyticAt ℝ f v) :
    AnalyticAt ℝ (fun w => c * f w) v := by
  exact ckAnalyticAt_mul analyticAt_const hf

private theorem ckAnalyticAt_neg
    {f : CKPhase → ℝ} {v : CKPhase}
    (hf : AnalyticAt ℝ f v) :
    AnalyticAt ℝ (fun w => -f w) v := by
  convert! hf.neg using 1

private theorem ckAnalyticAt_div
    {f g : CKPhase → ℝ} {v : CKPhase}
    (hf : AnalyticAt ℝ f v) (hg : AnalyticAt ℝ g v) (hg0 : g v ≠ 0) :
    AnalyticAt ℝ (fun w => f w / g w) v := by
  convert! hf.div hg hg0 using 1

/-- The polynomial scalar-point map `(x,y,z) ↦ (y,Γ₀(y,z))` is
analytic. -/
theorem analyticAt_ckScalarPoint (v : CKPhase) :
    AnalyticAt ℝ ckScalarPoint v := by
  have hy := analyticAt_ckPhase_coord (1 : Fin 7) v
  have hval := analyticAt_ckPhase_coord (2 : Fin 7) v
  have hdx := analyticAt_ckPhase_coord (3 : Fin 7) v
  have hdy := analyticAt_ckPhase_coord (4 : Fin 7) v
  have hg2 : AnalyticAt ℝ
      (fun w : CKPhase => gamma2 (w 1) (ckPhaseJet w)) v := by
    have hquot : AnalyticAt ℝ
        (fun w : CKPhase => (w 1 * w 4) / 2) v := by
      exact ckAnalyticAt_div_const 2 (ckAnalyticAt_mul hy hdy)
    have hraw : AnalyticAt ℝ
        (fun w : CKPhase => w 2 + w 1 * w 4 / 2) v := by
      exact ckAnalyticAt_add hval hquot
    simpa only [gamma2, ckPhaseJet] using hraw
  have hg0 : AnalyticAt ℝ
      (fun w : CKPhase => gamma0 (w 1) (ckPhaseJet w)) v := by
    have htwo := ckAnalyticAt_const_mul 2 hdx
    have hmiddle : AnalyticAt ℝ
        (fun w : CKPhase => w 1 ^ 2 * w 3 ^ 2) v := by
      exact ckAnalyticAt_mul (ckAnalyticAt_pow hy 2) (ckAnalyticAt_pow hdx 2)
    have hfour := ckAnalyticAt_const_mul 4 (ckAnalyticAt_pow hg2 2)
    have hraw : AnalyticAt ℝ
        (fun w : CKPhase => 2 * w 3 + w 1 ^ 2 * w 3 ^ 2 +
          4 * gamma2 (w 1) (ckPhaseJet w) ^ 2) v := by
      exact ckAnalyticAt_add (ckAnalyticAt_add htwo hmiddle) hfour
    simpa only [gamma0, ckPhaseJet] using hraw
  exact hy.prod hg0

/-- `U_q` places the scalar point in the explicit analytic region. -/
theorem ckScalarPoint_mem_scalarAnalyticRegion
    {P : Params} {v : CKPhase} (hU : CKPhaseInU P v) :
    ckScalarPoint v ∈ scalarAnalyticRegion P := by
  exact scalarPoint_mem_scalarAnalyticRegion_of_inU hU

/-- The three scalar-data coordinates, after composition with `(y,Γ₀)`,
are analytic at every phase point in `U_q`. -/
theorem analyticAt_ckScalarData
    {P : Params} {v : CKPhase} (hU : CKPhaseInU P v) :
    AnalyticAt ℝ
        (fun w : CKPhase =>
          (scalarDataAt P (w 1) (gamma0 (w 1) (ckPhaseJet w))).S) v ∧
      AnalyticAt ℝ
        (fun w : CKPhase =>
          (scalarDataAt P (w 1) (gamma0 (w 1) (ckPhaseJet w))).dSdt) v ∧
      AnalyticAt ℝ
        (fun w : CKPhase =>
          (scalarDataAt P (w 1) (gamma0 (w 1) (ckPhaseJet w))).dSdd) v := by
  have hpoint := analyticAt_ckScalarPoint v
  have hmem := ckScalarPoint_mem_scalarAnalyticRegion hU
  have hSbase := analyticAt_stildeUncurried_of_mem hmem
  have hTbase := analyticAt_stildePartialT_of_mem hmem
  have hDbase := analyticAt_stildePartialD_of_mem hmem
  constructor
  · change AnalyticAt ℝ (stildeUncurried P ∘ ckScalarPoint) v
    exact hSbase.comp hpoint
  constructor
  · change AnalyticAt ℝ
      ((fun z : ℝ × ℝ => deriv (fun t => Stilde P t z.2) z.1) ∘
        ckScalarPoint) v
    exact hTbase.comp hpoint
  · change AnalyticAt ℝ
      ((fun z : ℝ × ℝ => deriv (Stilde P z.1) z.2) ∘ ckScalarPoint) v
    exact hDbase.comp hpoint

/-- The leading coefficient, as a function of phase coordinates, is analytic
on `U_q`. -/
theorem analyticAt_ckCoeff0
    {P : Params} {v : CKPhase} (hU : CKPhaseInU P v) :
    AnalyticAt ℝ
      (fun w : CKPhase => coeff0 (w 1) (ckPhaseJet w)
        (scalarDataAt P (w 1) (gamma0 (w 1) (ckPhaseJet w)))) v := by
  have hy := analyticAt_ckPhase_coord (1 : Fin 7) v
  have hdx := analyticAt_ckPhase_coord (3 : Fin 7) v
  have hS := (analyticAt_ckScalarData hU).1
  have hD := (analyticAt_ckScalarData hU).2.2
  have hg1 : AnalyticAt ℝ
      (fun w : CKPhase => gamma1 (w 1) (ckPhaseJet w)) v := by
    have hprod : AnalyticAt ℝ
        (fun w : CKPhase => w 1 ^ 2 * w 3) v := by
      exact ckAnalyticAt_mul (ckAnalyticAt_pow hy 2) hdx
    have hraw : AnalyticAt ℝ
        (fun w : CKPhase => 1 + w 1 ^ 2 * w 3) v := by
      exact ckAnalyticAt_add analyticAt_const hprod
    simpa only [gamma1, ckPhaseJet] using hraw
  have hfirst : AnalyticAt ℝ
      (fun w : CKPhase => w 1 ^ 2 *
        (scalarDataAt P (w 1) (gamma0 (w 1) (ckPhaseJet w))).S) v := by
    exact ckAnalyticAt_mul (ckAnalyticAt_pow hy 2) hS
  have hsecondBase : AnalyticAt ℝ
      (fun w : CKPhase => gamma1 (w 1) (ckPhaseJet w) ^ 2 *
        (scalarDataAt P (w 1) (gamma0 (w 1) (ckPhaseJet w))).dSdd) v := by
    exact ckAnalyticAt_mul (ckAnalyticAt_pow hg1 2) hD
  have hsecond := ckAnalyticAt_const_mul 2 hsecondBase
  have hraw : AnalyticAt ℝ
      (fun w : CKPhase =>
        w 1 ^ 2 * (scalarDataAt P (w 1)
          (gamma0 (w 1) (ckPhaseJet w))).S +
        2 * (gamma1 (w 1) (ckPhaseJet w) ^ 2 *
          (scalarDataAt P (w 1)
            (gamma0 (w 1) (ckPhaseJet w))).dSdd)) v := by
    exact ckAnalyticAt_add hfirst hsecond
  apply hraw.congr
  exact Filter.Eventually.of_forall fun w => by
    simp only [coeff0]
    ring

/-- The first mixed coefficient is analytic on `U_q`. -/
theorem analyticAt_ckCoeff1
    {P : Params} {v : CKPhase} (hU : CKPhaseInU P v) :
    AnalyticAt ℝ
      (fun w : CKPhase => coeff1 (w 1) (ckPhaseJet w)
        (scalarDataAt P (w 1) (gamma0 (w 1) (ckPhaseJet w)))) v := by
  have hy := analyticAt_ckPhase_coord (1 : Fin 7) v
  have hval := analyticAt_ckPhase_coord (2 : Fin 7) v
  have hdx := analyticAt_ckPhase_coord (3 : Fin 7) v
  have hdy := analyticAt_ckPhase_coord (4 : Fin 7) v
  have hD := (analyticAt_ckScalarData hU).2.2
  have hg1 : AnalyticAt ℝ
      (fun w : CKPhase => gamma1 (w 1) (ckPhaseJet w)) v := by
    have hprod : AnalyticAt ℝ
        (fun w : CKPhase => w 1 ^ 2 * w 3) v := by
      exact ckAnalyticAt_mul (ckAnalyticAt_pow hy 2) hdx
    have hraw : AnalyticAt ℝ
        (fun w : CKPhase => 1 + w 1 ^ 2 * w 3) v := by
      exact ckAnalyticAt_add analyticAt_const hprod
    simpa only [gamma1, ckPhaseJet] using hraw
  have hg2 : AnalyticAt ℝ
      (fun w : CKPhase => gamma2 (w 1) (ckPhaseJet w)) v := by
    have hquot : AnalyticAt ℝ
        (fun w : CKPhase => w 1 * w 4 / 2) v := by
      exact ckAnalyticAt_div_const 2 (ckAnalyticAt_mul hy hdy)
    have hraw : AnalyticAt ℝ
        (fun w : CKPhase => w 2 + w 1 * w 4 / 2) v := by
      exact ckAnalyticAt_add hval hquot
    simpa only [gamma2, ckPhaseJet] using hraw
  have hbase : AnalyticAt ℝ
      (fun w : CKPhase => w 1 * gamma1 (w 1) (ckPhaseJet w) *
        gamma2 (w 1) (ckPhaseJet w) *
        (scalarDataAt P (w 1) (gamma0 (w 1) (ckPhaseJet w))).dSdd) v := by
    exact ckAnalyticAt_mul
      (ckAnalyticAt_mul (ckAnalyticAt_mul hy hg1) hg2) hD
  have hraw := ckAnalyticAt_const_mul 4 hbase
  apply hraw.congr
  exact Filter.Eventually.of_forall fun w => by
    simp only [coeff1]
    ring

/-- The pure-`y` coefficient is analytic on `U_q`. -/
theorem analyticAt_ckCoeff2
    {P : Params} {v : CKPhase} (hU : CKPhaseInU P v) :
    AnalyticAt ℝ
      (fun w : CKPhase => coeff2 (w 1) (ckPhaseJet w)
        (scalarDataAt P (w 1) (gamma0 (w 1) (ckPhaseJet w)))) v := by
  have hy := analyticAt_ckPhase_coord (1 : Fin 7) v
  have hval := analyticAt_ckPhase_coord (2 : Fin 7) v
  have hdy := analyticAt_ckPhase_coord (4 : Fin 7) v
  have hS := (analyticAt_ckScalarData hU).1
  have hD := (analyticAt_ckScalarData hU).2.2
  have hg2 : AnalyticAt ℝ
      (fun w : CKPhase => gamma2 (w 1) (ckPhaseJet w)) v := by
    have hquot : AnalyticAt ℝ
        (fun w : CKPhase => w 1 * w 4 / 2) v := by
      exact ckAnalyticAt_div_const 2 (ckAnalyticAt_mul hy hdy)
    have hraw : AnalyticAt ℝ
        (fun w : CKPhase => w 2 + w 1 * w 4 / 2) v := by
      exact ckAnalyticAt_add hval hquot
    simpa only [gamma2, ckPhaseJet] using hraw
  have hDterm : AnalyticAt ℝ
      (fun w : CKPhase => gamma2 (w 1) (ckPhaseJet w) ^ 2 *
        (scalarDataAt P (w 1) (gamma0 (w 1) (ckPhaseJet w))).dSdd) v := by
    exact ckAnalyticAt_mul (ckAnalyticAt_pow hg2 2) hD
  have hDterm8 := ckAnalyticAt_const_mul 8 hDterm
  have hinner : AnalyticAt ℝ
      (fun w : CKPhase =>
        (scalarDataAt P (w 1) (gamma0 (w 1) (ckPhaseJet w))).S +
          8 * (gamma2 (w 1) (ckPhaseJet w) ^ 2 *
            (scalarDataAt P (w 1)
              (gamma0 (w 1) (ckPhaseJet w))).dSdd)) v := by
    exact ckAnalyticAt_add hS hDterm8
  have hraw : AnalyticAt ℝ
      (fun w : CKPhase => w 1 ^ 2 *
        ((scalarDataAt P (w 1) (gamma0 (w 1) (ckPhaseJet w))).S +
          8 * (gamma2 (w 1) (ckPhaseJet w) ^ 2 *
            (scalarDataAt P (w 1)
              (gamma0 (w 1) (ckPhaseJet w))).dSdd))) v := by
    exact ckAnalyticAt_mul (ckAnalyticAt_pow hy 2) hinner
  apply hraw.congr
  exact Filter.Eventually.of_forall fun w => by
    simp only [coeff2]
    ring

/-- The lower-order term in (3.16) is analytic on `U_q`. -/
theorem analyticAt_ckLowerOrder
    {P : Params} {v : CKPhase} (hU : CKPhaseInU P v) :
    AnalyticAt ℝ
      (fun w : CKPhase => lowerOrder P (w 1) (ckPhaseJet w)
        (scalarDataAt P (w 1) (gamma0 (w 1) (ckPhaseJet w)))) v := by
  have hy := analyticAt_ckPhase_coord (1 : Fin 7) v
  have hval := analyticAt_ckPhase_coord (2 : Fin 7) v
  have hdx := analyticAt_ckPhase_coord (3 : Fin 7) v
  have hdy := analyticAt_ckPhase_coord (4 : Fin 7) v
  have hS := (analyticAt_ckScalarData hU).1
  have hT := (analyticAt_ckScalarData hU).2.1
  have hD := (analyticAt_ckScalarData hU).2.2
  have hg1 : AnalyticAt ℝ
      (fun w : CKPhase => gamma1 (w 1) (ckPhaseJet w)) v := by
    have hprod : AnalyticAt ℝ
        (fun w : CKPhase => w 1 ^ 2 * w 3) v :=
      ckAnalyticAt_mul (ckAnalyticAt_pow hy 2) hdx
    have hraw : AnalyticAt ℝ
        (fun w : CKPhase => 1 + w 1 ^ 2 * w 3) v :=
      ckAnalyticAt_add analyticAt_const hprod
    simpa only [gamma1, ckPhaseJet] using hraw
  have hg2 : AnalyticAt ℝ
      (fun w : CKPhase => gamma2 (w 1) (ckPhaseJet w)) v := by
    have hquot : AnalyticAt ℝ
        (fun w : CKPhase => w 1 * w 4 / 2) v :=
      ckAnalyticAt_div_const 2 (ckAnalyticAt_mul hy hdy)
    have hraw : AnalyticAt ℝ
        (fun w : CKPhase => w 2 + w 1 * w 4 / 2) v :=
      ckAnalyticAt_add hval hquot
    simpa only [gamma2, ckPhaseJet] using hraw
  have hfirstLeft := ckAnalyticAt_const_mul 3 (ckAnalyticAt_mul hy hS)
  have hfirstRight := ckAnalyticAt_const_mul 24
    (ckAnalyticAt_mul (ckAnalyticAt_mul hy (ckAnalyticAt_pow hg2 2)) hD)
  have hfirstInner := ckAnalyticAt_add hfirstLeft hfirstRight
  have hfirst := ckAnalyticAt_mul hfirstInner hdy
  have hsecond := ckAnalyticAt_const_mul 4
    (ckAnalyticAt_mul
      (ckAnalyticAt_mul (ckAnalyticAt_mul (ckAnalyticAt_pow hy 2) hg2) hD)
      (ckAnalyticAt_pow hdx 2))
  have hthird := ckAnalyticAt_const_mul 8
    (ckAnalyticAt_mul (ckAnalyticAt_mul (ckAnalyticAt_mul hg1 hg2) hD) hdx)
  have hfourth := ckAnalyticAt_const_mul 2
    (ckAnalyticAt_mul (ckAnalyticAt_mul hy hg2) hT)
  have hfifth := ckAnalyticAt_const_mul (2 * (1 - 2 / P.p))
    (ckAnalyticAt_mul hS hg2)
  have hraw := ckAnalyticAt_add
    (ckAnalyticAt_add
      (ckAnalyticAt_add (ckAnalyticAt_add hfirst hsecond) hthird) hfourth)
    hfifth
  apply hraw.congr
  exact Filter.Eventually.of_forall fun w => by
    simp only [lowerOrder, ckPhaseJet]
    ring

/-- The CK normal form `G` is real analytic at every point of `U_q`. -/
theorem analyticAt_ckNormalForm
    {P : Params} {v : CKPhase} (hU : CKPhaseInU P v) :
    AnalyticAt ℝ (ckNormalForm P) v := by
  have hc0 := analyticAt_ckCoeff0 hU
  have hc1 := analyticAt_ckCoeff1 hU
  have hc2 := analyticAt_ckCoeff2 hU
  have hL := analyticAt_ckLowerOrder hU
  have hz4 := analyticAt_ckPhase_coord (5 : Fin 7) v
  have hz5 := analyticAt_ckPhase_coord (6 : Fin 7) v
  have hnum := ckAnalyticAt_add
    (ckAnalyticAt_add
      (ckAnalyticAt_const_mul 2 (ckAnalyticAt_mul hc1 hz4))
      (ckAnalyticAt_mul hc2 hz5)) hL
  have hc0ne : coeff0 (v 1) (ckPhaseJet v)
      (scalarDataAt P (v 1) (gamma0 (v 1) (ckPhaseJet v))) ≠ 0 :=
    (coeff0_scalarDataOfJet_pos_of_inU P hU).ne'
  have hquot := ckAnalyticAt_div (ckAnalyticAt_neg hnum) hc0 hc0ne
  apply hquot.congr
  exact Filter.Eventually.of_forall fun w => by
    simp only [ckNormalForm, normalForm, ckPhaseJet]
    ring

/-- The normal form is analytic on a neighborhood of every phase point in
`U_q`. -/
theorem analyticOnNhd_ckNormalForm_inU (P : Params) :
    AnalyticOnNhd ℝ (ckNormalForm P) {v : CKPhase | CKPhaseInU P v} := by
  intro v hv
  exact analyticAt_ckNormalForm hv

end

end StressTensor
