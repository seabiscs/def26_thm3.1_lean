import StressTensor.DifferentialBridge

/-!
# Bridge from the ansatz to the original energy-gradient stress

The algebraic stress factorization in `StressTensor.Ansatz` is phrased in
terms of a recorded jet.  This file identifies that jet-level gradient with
the actual partial derivatives of `u(x,y) = x + y² γ(x,y)`, defines the
original energy-gradient stress from those partial derivatives, and compares
it pointwise with the factored singular stress used in
`StressTensor.DifferentialBridge`.

Every differentiability, positivity, and off-axis assumption needed by the
comparison is explicit.  The final local lemma transfers the ordinary
divergence across the pointwise equality on an open neighborhood.
-/

namespace StressTensor

noncomputable section

/-! ## The actual gradient of the ansatz -/

/-- The two actual partial derivatives of the ansatz, represented using
Mathlib's total derivative. -/
def actualAnsatzGradient (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ × ℝ :=
  (partialX (ansatz γ) x y, partialY (ansatz γ) x y)

/-- The actual `x` derivative of the ansatz is `Γ₁`. -/
theorem partialX_ansatz_eq_gamma1
    {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hx : DifferentiableAt ℝ (fun ξ => γ ξ y) x) :
    partialX (ansatz γ) x y = gamma1 y (jetOf γ x y) := by
  have h := hasDerivAt_ansatz_x_eq_gamma1 (z := jetOf γ x y)
    hx.hasDerivAt rfl
  exact h.deriv

/-- The actual `y` derivative of the ansatz is `2yΓ₂`. -/
theorem partialY_ansatz_eq_two_mul_gamma2
    {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hy : DifferentiableAt ℝ (γ x) y) :
    partialY (ansatz γ) x y = 2 * y * gamma2 y (jetOf γ x y) := by
  have h := hasDerivAt_ansatz_y_eq_gamma2 (z := jetOf γ x y)
    hy.hasDerivAt rfl rfl
  exact h.deriv

/-- Under the two first-order differentiability assumptions, the actual
gradient of the ansatz is exactly the jet-level `ansatzGradient`. -/
theorem actualAnsatzGradient_eq_ansatzGradient
    {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (hx : DifferentiableAt ℝ (fun ξ => γ ξ y) x)
    (hy : DifferentiableAt ℝ (γ x) y) :
    actualAnsatzGradient γ x y = ansatzGradient y (jetOf γ x y) := by
  ext
  · exact partialX_ansatz_eq_gamma1 hx
  · exact partialY_ansatz_eq_two_mul_gamma2 hy

/-! ## The original and factored stress fields -/

/-- The scalar multiplier in
`∂ J̃_q(Du) = |Du|^(q-2) Du / (1-|Du|^q)^(1-1/q)`, expressed through
the squared norm of the actual ansatz gradient. -/
def energyGradientStressScalar
    (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  Real.rpow (normSq (actualAnsatzGradient γ x y)) ((P.q - 2) / 2) /
    Real.rpow
      (1 - Real.rpow (normSq (actualAnsatzGradient γ x y)) (P.q / 2))
      (1 - 1 / P.q)

/-- The original energy-gradient stress field evaluated on the actual ansatz
gradient. -/
def energyGradientStress
    (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ × ℝ :=
  energyGradientStressScalar P γ x y • actualAnsatzGradient γ x y

/-- The factored singular stress field as a pair. -/
def singularStress
    (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ × ℝ :=
  (singularStressX P γ x y, singularStressY P γ x y)

/-- The exact conditions needed at one point to identify the original stress
with its factored singular form. -/
def StressFactorizationAdmissibleAt
    (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) : Prop :=
  DifferentiableAt ℝ (fun ξ => γ ξ y) x ∧
    DifferentiableAt ℝ (γ x) y ∧
    y ≠ 0 ∧
    0 < 1 + y ^ 2 * gamma0 y (jetOf γ x y) ∧
    0 < Ccomp P y (jetOf γ x y)

/-- Pointwise equality between the original energy-gradient stress and the
factored singular stress, away from the light axis. -/
theorem energyGradientStress_eq_singularStress
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (h : StressFactorizationAdmissibleAt P γ x y) :
    energyGradientStress P γ x y = singularStress P γ x y := by
  rcases h with ⟨hx, hy, hy0, hbase, hC⟩
  have hgradient := actualAnsatzGradient_eq_ansatzGradient hx hy
  have hfactor := stressVector_factorization P y (jetOf γ x y) hy0 hbase hC
  rw [energyGradientStress, energyGradientStressScalar, hgradient]
  rw [hfactor]
  have hdenom : singularDenominator P y ≠ 0 := by
    exact (Real.rpow_pos_of_pos (abs_pos.mpr hy0) (2 / P.p)).ne'
  ext <;>
    simp only [singularStress, singularStressX, singularStressY,
      singularDenominator, Scomp, scalarField, scalarDataField,
      scalarDataOfJet, scalarDataAt, gamma1Field, gamma2Field,
      ansatzGradient, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    field_simp

theorem energyGradientStress_fst_eq_singularStressX
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (h : StressFactorizationAdmissibleAt P γ x y) :
    (energyGradientStress P γ x y).1 = singularStressX P γ x y := by
  exact congrArg Prod.fst (energyGradientStress_eq_singularStress h)

theorem energyGradientStress_snd_eq_singularStressY
    {P : Params} {γ : ℝ → ℝ → ℝ} {x y : ℝ}
    (h : StressFactorizationAdmissibleAt P γ x y) :
    (energyGradientStress P γ x y).2 = singularStressY P γ x y := by
  exact congrArg Prod.snd (energyGradientStress_eq_singularStress h)

/-- Pointwise admissibility on a set gives equality of the two stress fields
on that set. -/
theorem energyGradientStress_eqOn_singularStress
    {P : Params} {γ : ℝ → ℝ → ℝ} {U : Set Point}
    (hU : ∀ w : Point, w ∈ U →
      StressFactorizationAdmissibleAt P γ w.1 w.2) :
    Set.EqOn
      (fun w : Point => energyGradientStress P γ w.1 w.2)
      (fun w : Point => singularStress P γ w.1 w.2) U := by
  rintro ⟨x, y⟩ hxy
  exact energyGradientStress_eq_singularStress (hU (x, y) hxy)

/-! ## Transfer of divergence across a local equality -/

/-- The ordinary coordinate divergence of the original energy-gradient
stress. -/
def energyGradientStressDivergence
    (P : Params) (γ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun ξ => (energyGradientStress P γ ξ y).1) x +
    deriv (fun η => (energyGradientStress P γ x η).2) y

/-- Equality of the two stress fields on an open neighborhood transfers their
ordinary divergence at every point of that neighborhood. -/
theorem energyGradientStressDivergence_eq_singularStressDivergence_of_isOpen
    {P : Params} {γ : ℝ → ℝ → ℝ} {U : Set Point} {x y : ℝ}
    (hUopen : IsOpen U) (hxy : (x, y) ∈ U)
    (hadm : ∀ w : Point, w ∈ U →
      StressFactorizationAdmissibleAt P γ w.1 w.2) :
    energyGradientStressDivergence P γ x y =
      singularStressDivergence P γ x y := by
  have heq := energyGradientStress_eqOn_singularStress (P := P) (γ := γ) hadm
  have hopenX : IsOpen {ξ : ℝ | (ξ, y) ∈ U} := by
    exact hUopen.preimage (continuous_id.prodMk continuous_const)
  have hopenY : IsOpen {η : ℝ | (x, η) ∈ U} := by
    exact hUopen.preimage (continuous_const.prodMk continuous_id)
  have heqX :
      (fun ξ => (energyGradientStress P γ ξ y).1) =ᶠ[nhds x]
        (fun ξ => singularStressX P γ ξ y) := by
    apply Filter.eventuallyEq_of_mem (hopenX.mem_nhds hxy)
    intro ξ hξ
    exact congrArg Prod.fst (heq hξ)
  have heqY :
      (fun η => (energyGradientStress P γ x η).2) =ᶠ[nhds y]
        (fun η => singularStressY P γ x η) := by
    apply Filter.eventuallyEq_of_mem (hopenY.mem_nhds hxy)
    intro η hη
    exact congrArg Prod.snd (heq hη)
  rw [energyGradientStressDivergence, singularStressDivergence,
    heqX.deriv_eq, heqY.deriv_eq]

end

end StressTensor
