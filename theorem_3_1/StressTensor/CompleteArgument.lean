import StressTensor.CKCompleteOutcome
import StressTensor.FinalArgument

/-!
# The complete stress-tensor argument

This module closes the last gap between the unconditional local
Cauchy--Kowalevskaya construction and the geometric conclusion of the
argument.  For every choice of parameters it supplies positive reconstruction
radii, the actual local analytic solution, a compact square localization, the
off-axis stress-divergence equation, the unique maximal horizontal light ray,
and reflection symmetry of the reconstructed solution.
-/

namespace StressTensor
namespace CompleteArgument

noncomputable section

/-- Every centered reconstruction box is invariant under reflection in the
transverse coordinate. -/
theorem ySymmetric_reconstructionBox (rx ry : ℝ) :
    YSymmetric (reconstructionBox rx ry) := by
  intro x y
  simp only [mem_reconstructionBox, abs_neg]

/-- The fully assembled conclusion of the stress-tensor argument.

Starting only from `P : Params`, this theorem produces:

* positive radii and an actual local `CKOutcome` on the centered box;
* a compact square on which the original stress divergence vanishes off the
  light axis;
* the horizontal diameter as a maximally extended light segment, unique as
  an unoriented segment; and
* evenness of the analytic scalar field in the transverse coordinate on the
  whole reconstruction box.
-/
theorem exists_complete_argument (P : Params) :
    ∃ rx ry : ℝ,
      0 < rx ∧ 0 < ry ∧
      ∃ K : CKOutcome P (reconstructionBox rx ry) ry,
      ∃ L : CompactSquareLocalization P K.gamma
          (reconstructionBox rx ry),
        (∀ {w : Point}, w ∈ openSquare L.ell → w.2 ≠ 0 →
          energyGradientStressDivergence P K.gamma w.1 w.2 = 0) ∧
        IsMaximallyExtendedLightSegment (openSquare L.ell)
          (fun w => ansatz K.gamma w.1 w.2)
          (horizontalLeft L.ell) (horizontalRight L.ell) ∧
        (∀ {a b : Point},
          IsMaximallyExtendedLightSegment (openSquare L.ell)
            (fun w => ansatz K.gamma w.1 w.2) a b →
          closedSegment a b = horizontalDiameter L.ell) ∧
        (∀ w ∈ reconstructionBox rx ry,
          K.gamma w.1 (-w.2) = K.gamma w.1 w.2) := by
  let D := CKCompleteOutcome.positiveCKOutcomeData P
  obtain ⟨L, hdiv, hhorizontal, hunique⟩ :=
    D.outcome.exists_localized_final_argument
  refine ⟨D.rx, D.ry, D.rx_pos, D.ry_pos, D.outcome, L,
    hdiv, hhorizontal, hunique, ?_⟩
  exact D.outcome.even_on_symmetric_domain
    (ySymmetric_reconstructionBox D.rx D.ry)

end

end CompleteArgument
end StressTensor
