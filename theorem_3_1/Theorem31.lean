import Section33DenseEuler

/-!
# Theorem 3.1

The conclusion below follows the manuscript boundary: a positive square,
an analytic `W^{1,∞}` map with unit gradient, the weak Euler identity,
weak-Lorentz control of the stress, variational maximality, and the unique
horizontal maximal light ray.
-/

open Filter MeasureTheory Set Topology

noncomputable section

namespace Theorem31

open GammaMaximalityBridge MaximalityOfU StressTensor

/-- Measurable distribution-function presentation of weak `L^r` on the
finite square. -/
def HasWeakLpOn (r : ℝ) (ell : ℝ) (F : Plane → PlaneVector) : Prop :=
  AEStronglyMeasurable F
      (volume.restrict (MaximalityOfU.cube ell)) ∧
    HasWeakLpTailOn volume r (MaximalityOfU.cube ell) F

/-- All assertions made in Theorem 3.1, bundled around the concrete
representatives introduced in `Theorem31Packaging`. -/
structure Theorem31Conclusion (q : ℝ) where
  P : Params
  q_eq : P.q = q
  core : GeometricCore P
  ell_pos : 0 < core.L.ell
  u : W1InfinityMap core.L.ell
  u_eq_ansatz : u = ansatzW1InfinityMap core
  analytic_u : AnalyticOnNhd ℝ u.toFun (closedSquare core.L.ell)
  gradient_eq_actual : ∀ z, z ∈ closedSquare core.L.ell →
    u.gradient z = BornInfeldSubgradient.pairToVector
      (actualAnsatzGradient core.K.gamma z.1 z.2)
  gradient_le_one_on_closed_square :
    ∀ z, z ∈ closedSquare core.L.ell → ‖u.gradient z‖ ≤ 1
  gradient_lt_one_off_axis :
    ∀ z, z ∈ openSquare core.L.ell → z.2 ≠ 0 →
      ‖u.gradient z‖ < 1
  value_on_light_ray : ∀ x, |x| ≤ core.L.ell → u.toFun (x, 0) = x
  weak_euler : ∀ phi : W11ZeroW1InfinityTest core.L.ell,
    (∫ z in MaximalityOfU.cube core.L.ell,
      inner ℝ (stressField P core.K.gamma z) (phi.map.gradient z)) = 0
  stress_eq_energy_gradient_off_axis :
    ∀ z, z ∈ closedSquare core.L.ell → z.2 ≠ 0 →
      stressField P core.K.gamma z =
        BornInfeldSubgradient.pairToVector
          (energyGradientStress P core.K.gamma z.1 z.2)
  stress_weak_Lp : HasWeakLpOn
    (q / (2 * (q - 1))) core.L.ell (stressField P core.K.gamma)
  maximality : IsBornInfeldMaximizer q u
  horizontal_is_maximal_light_ray : IsMaximallyExtendedLightSegment
    (openSquare core.L.ell) u.toFun
    (horizontalLeft core.L.ell) (horizontalRight core.L.ell)
  unique_maximal_light_ray : ∀ {a b : Plane},
    IsMaximallyExtendedLightSegment
      (openSquare core.L.ell) u.toFun a b →
    closedSegment a b = horizontalDiameter core.L.ell

/-- Final assembly once the dense weak Euler theorem has been supplied.
Every other assertion is already unconditional. -/
theorem exists_theorem31_of_weakEuler
    (q : ℝ) (hq1 : 1 < q) (hq2 : q < 2)
    (hEuler : ∀ phi : W11ZeroW1InfinityTest
      (canonicalGeometricCore (Params.ofQ q hq1 hq2)).L.ell,
      (∫ z in MaximalityOfU.cube
          (canonicalGeometricCore (Params.ofQ q hq1 hq2)).L.ell,
        inner ℝ
          (stressField (Params.ofQ q hq1 hq2)
            (canonicalGeometricCore (Params.ofQ q hq1 hq2)).K.gamma z)
          (phi.map.gradient z)) = 0) :
    Nonempty (Theorem31Conclusion q) := by
  let P := Params.ofQ q hq1 hq2
  let G := canonicalGeometricCore P
  let u := ansatzW1InfinityMap G
  have hweakLpP : HasWeakLpOn
      (P.q / (2 * (P.q - 1))) G.L.ell
      (stressField P G.K.gamma) := by
    exact localized_stressField_measurable_and_has_weak_paper_tail
      G.L G.K.solution.1
  have hweakLp : HasWeakLpOn
      (q / (2 * (q - 1))) G.L.ell
      (stressField P G.K.gamma) := by
    simpa only [P, Params.ofQ_q] using hweakLpP
  have hmax : IsBornInfeldMaximizer q u := by
    simpa only [P, Params.ofQ_q, u] using
      ansatz_isBornInfeldMaximizer_of_weakEuler G hEuler
  refine ⟨
    { P := P
      q_eq := Params.ofQ_q q hq1 hq2
      core := G
      ell_pos := G.L.ell_pos
      u := u
      u_eq_ansatz := rfl
      analytic_u := ansatzMap_analyticOnNhd_closedSquare G
      gradient_eq_actual :=
        fun z hz => (pairToVector_actualAnsatzGradient_eq G hz).symm
      gradient_le_one_on_closed_square := ?_
      gradient_lt_one_off_axis := ?_
      value_on_light_ray := ?_
      weak_euler := hEuler
      stress_eq_energy_gradient_off_axis :=
        fun z hz hy => stressField_eq_pairToVector_energyGradientStress G hz hy
      stress_weak_Lp := hweakLp
      maximality := hmax
      horizontal_is_maximal_light_ray := ?_
      unique_maximal_light_ray := ?_ }⟩
  · intro z hz
    exact ansatzGradient_norm_le_one G hz
  · intro z hz hy
    exact ansatzGradient_norm_lt_one_off_axis G hz hy
  · intro x _hx
    exact ansatzMap_on_axis G.K.gamma x
  · change IsMaximallyExtendedLightSegment
      (openSquare G.L.ell) (fun z => ansatz G.K.gamma z.1 z.2)
      (horizontalLeft G.L.ell) (horizontalRight G.L.ell)
    exact G.horizontal_is_maximal
  · intro a b hlight
    apply G.unique_maximal
    change IsMaximallyExtendedLightSegment
      (openSquare G.L.ell) (fun z => ansatz G.K.gamma z.1 z.2) a b
    exact hlight

/-- The unconditional paper-facing theorem.  The analytic construction,
localization, stress estimates, removable-axis Euler identity, convex
subgradient argument, and light-ray classification have all been discharged
in the imported modules. -/
theorem theorem31 (q : ℝ) (hq1 : 1 < q) (hq2 : q < 2) :
    Nonempty (Theorem31Conclusion q) := by
  let P := Params.ofQ q hq1 hq2
  let G := canonicalGeometricCore P
  apply exists_theorem31_of_weakEuler q hq1 hq2
  exact dense_weakEuler G.K G.L

end Theorem31
