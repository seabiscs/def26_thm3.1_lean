import StressTensor.LightRayBridge
import StressTensor.ReflectionBridge

/-!
# End-to-end conclusion after Cauchy--Kowalevskaya

Every manuscript-specific step after local analytic existence is collected
here.  Given the explicit `CKOutcome` produced by the cited
Cauchy--Kowalevskaya theorem, Lean constructs the compact square, proves the
original energy-gradient stress divergence-free away from the light axis,
and proves that the horizontal diameter is the unique maximally extended
light ray.
-/

namespace StressTensor

noncomputable section

/-- The complete localized conclusion of the attached argument, with the
Cauchy--Kowalevskaya output as its only input. -/
theorem CKOutcome.exists_localized_final_argument
    {P : Params} {U : Set Point} {r : ℝ} (K : CKOutcome P U r) :
    ∃ L : CompactSquareLocalization P K.gamma U,
      (∀ {w : Point}, w ∈ openSquare L.ell → w.2 ≠ 0 →
        energyGradientStressDivergence P K.gamma w.1 w.2 = 0) ∧
      IsMaximallyExtendedLightSegment (openSquare L.ell)
        (fun w => ansatz K.gamma w.1 w.2)
        (horizontalLeft L.ell) (horizontalRight L.ell) ∧
      (∀ {a b : Point},
        IsMaximallyExtendedLightSegment (openSquare L.ell)
          (fun w => ansatz K.gamma w.1 w.2) a b →
        closedSegment a b = horizontalDiameter L.ell) := by
  rcases K.exists_compactSquareLocalization_of_analytic with ⟨L⟩
  refine ⟨L, ?_, ?_, ?_⟩
  · intro w hw hy
    exact L.energyGradientStressDivergence_eq_zero_off_axis
      K.solution.1 K.solution.2.1 hw hy
  · exact horizontalDiameter_isMaximallyExtendedLightSegment
      K.gamma L.ell_pos
  · intro a b hmax
    exact uniqueMaximalLightRay L K.solution.1 hmax

/-- On a symmetric CK domain, the same outcome also supplies the evenness
used in the manuscript before localization. -/
theorem CKOutcome.even_on_symmetric_domain
    {P : Params} {U : Set Point} {r : ℝ} (K : CKOutcome P U r)
    (hU : YSymmetric U) :
    ∀ w ∈ U, K.gamma w.1 (-w.2) = K.gamma w.1 w.2 := by
  rintro ⟨x, y⟩ hxy
  exact K.even_of_ySymmetric hU hxy

end

end StressTensor
