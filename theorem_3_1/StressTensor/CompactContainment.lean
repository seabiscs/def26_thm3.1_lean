import StressTensor.CKCompleteOutcome
import StressTensor.CompactLocalization

/-!
# Compact containment of the final local square

This module records the compact-containment sentence used between the local
Cauchy--Kowalevskaya construction and the stress-tensor conclusion.  The
notation `InQ P x y` is the formalization of membership in the manuscript's
open square `Q_{ρ}`.  Thus the theorem below says concretely that the closure
of the final open square is compact, lies in both the analytic solution box
and `Q_{ρ}`, and carries an actual jet lying in `U_q` at every point.
-/

namespace StressTensor
namespace CompactContainment

noncomputable section

/-- A compact-square localization realizes the manuscript's compact
containment statement: the closure of its open square is the closed square,
is compact, lies simultaneously in the CK domain and `Q_{ρ}`, and its actual
jet lies in `U_q` throughout that closure. -/
theorem of_localization
    {P : Params} {gamma : ℝ → ℝ → ℝ} {U : Set Point}
    (L : CompactSquareLocalization P gamma U) :
    closure (openSquare L.ell) = closedSquare L.ell ∧
      IsCompact (closure (openSquare L.ell)) ∧
      closure (openSquare L.ell) ⊆
        U ∩ {w : Point | InQ P w.1 w.2} ∧
      (∀ w ∈ closure (openSquare L.ell),
        InU P w.1 w.2 (jetOf gamma w.1 w.2)) := by
  have hclosure : closure (openSquare L.ell) = closedSquare L.ell :=
    closure_openSquare L.ell_pos
  refine ⟨hclosure, ?_, ?_, ?_⟩
  · rw [hclosure]
    exact L.isCompact
  · intro w hw
    rw [hclosure] at hw
    exact ⟨L.closed_subset_domain hw, (L.jet_inU w hw).1⟩
  · intro w hw
    rw [hclosure] at hw
    exact L.jet_inU w hw

/-- The half-side of every localized square is strictly smaller than the
parameter radius `ρ`; this is the explicit radial form of containment in
`Q_{ρ}`. -/
theorem ell_lt_rho
    {P : Params} {gamma : ℝ → ℝ → ℝ} {U : Set Point}
    (L : CompactSquareLocalization P gamma U) :
    L.ell < P.rho := by
  have hright : (L.ell, 0) ∈ closedSquare L.ell := by
    simp [closedSquare, abs_of_pos L.ell_pos, L.ell_pos.le]
  have hQ := (L.jet_inU (L.ell, 0) hright).1.1
  simpa [abs_of_pos L.ell_pos] using hQ

/-- When the CK domain is the centered reconstruction box, compact
containment also gives strict half-side inequalities against both of its
radii. -/
theorem ell_lt_reconstruction_radii
    {P : Params} {gamma : ℝ → ℝ → ℝ} {rx ry : ℝ}
    (L : CompactSquareLocalization P gamma (reconstructionBox rx ry)) :
    L.ell < rx ∧ L.ell < ry := by
  have hright : (L.ell, 0) ∈ closedSquare L.ell := by
    simp [closedSquare, abs_of_pos L.ell_pos, L.ell_pos.le]
  have htop : (0, L.ell) ∈ closedSquare L.ell := by
    simp [closedSquare, abs_of_pos L.ell_pos, L.ell_pos.le]
  have hx := mem_reconstructionBox.mp (L.closed_subset_domain hright) |>.1
  have hy := mem_reconstructionBox.mp (L.closed_subset_domain htop) |>.2
  exact ⟨by simpa [abs_of_pos L.ell_pos] using hx,
    by simpa [abs_of_pos L.ell_pos] using hy⟩

/-- Unconditional compact containment for the local analytic solution
constructed from `P`.  This is the direct formal counterpart of choosing a
smaller square compactly contained in the CK box and in `Q_{ρ}`, while its
full actual jet remains in `U_q` on the closed square. -/
theorem exists_constructed_local_square (P : Params) :
    ∃ rx ry : ℝ,
      0 < rx ∧ 0 < ry ∧
      ∃ K : CKOutcome P (reconstructionBox rx ry) ry,
      ∃ L : CompactSquareLocalization P K.gamma
          (reconstructionBox rx ry),
        L.ell < rx ∧ L.ell < ry ∧ L.ell < P.rho ∧
        closure (openSquare L.ell) = closedSquare L.ell ∧
        IsCompact (closure (openSquare L.ell)) ∧
        closure (openSquare L.ell) ⊆
          reconstructionBox rx ry ∩ {w : Point | InQ P w.1 w.2} ∧
        (∀ w ∈ closure (openSquare L.ell),
          InU P w.1 w.2 (jetOf K.gamma w.1 w.2)) := by
  let D := CKCompleteOutcome.positiveCKOutcomeData P
  obtain ⟨L⟩ := D.outcome.exists_compactSquareLocalization_of_analytic
  have hradii := ell_lt_reconstruction_radii L
  have hrho := ell_lt_rho L
  have hcontain := of_localization L
  exact ⟨D.rx, D.ry, D.rx_pos, D.ry_pos, D.outcome, L,
    hradii.1, hradii.2, hrho, hcontain.1, hcontain.2.1,
    hcontain.2.2.1, hcontain.2.2.2⟩

end

end CompactContainment
end StressTensor
