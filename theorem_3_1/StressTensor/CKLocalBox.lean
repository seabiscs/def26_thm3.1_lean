import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Centered boxes inside local neighborhoods

The analytic realization and uniqueness arguments naturally produce
properties that hold eventually at the origin.  This module extracts a
positive centered rectangle, while simultaneously shrinking it enough for
two prescribed geometric convergence rates.
-/

namespace StressTensor
namespace CKLocalBox

noncomputable section

/-- Every neighborhood of the origin in the plane contains a positive
centered open rectangle. -/
theorem exists_centeredBox_subset_of_mem_nhds_zero
    {s : Set (ℝ × ℝ)} (hs : s ∈ nhds ((0, 0) : ℝ × ℝ)) :
    ∃ rx ry : ℝ, 0 < rx ∧ 0 < ry ∧
      Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry ⊆ s := by
  rw [mem_nhds_prod_iff] at hs
  rcases hs with ⟨u, hu, v, hv, huv⟩
  rcases Metric.mem_nhds_iff.mp hu with ⟨rx, hrx, hxu⟩
  rcases Metric.mem_nhds_iff.mp hv with ⟨ry, hry, hyv⟩
  refine ⟨rx, ry, hrx, hry, ?_⟩
  intro z hz
  apply huv
  constructor
  · apply hxu
    simpa [Real.dist_eq] using (abs_lt.mpr hz.1)
  · apply hyv
    simpa [Real.dist_eq] using (abs_lt.mpr hz.2)

/-- A positive radius that places the enlarged geometric rate `s+1`
strictly inside its convergence threshold. -/
def safeRadius (s : ℝ) : ℝ := (2 * (s + 1))⁻¹

theorem safeRadius_pos {s : ℝ} (hs : 0 ≤ s) : 0 < safeRadius s := by
  unfold safeRadius
  positivity

theorem mul_safeRadius_lt_one {s : ℝ} (hs : 0 ≤ s) :
    (s + 1) * safeRadius s < 1 := by
  unfold safeRadius
  rw [← div_eq_mul_inv, div_lt_one (by positivity)]
  linarith

/-- A neighborhood of the origin contains a centered rectangle on which
both enlarged geometric rates are strictly convergent. -/
theorem exists_convergenceBox_subset_of_mem_nhds_zero
    {s : Set (ℝ × ℝ)} {sx sy : ℝ}
    (hsx : 0 ≤ sx) (hsy : 0 ≤ sy)
    (hs : s ∈ nhds ((0, 0) : ℝ × ℝ)) :
    ∃ rx ry : ℝ, 0 < rx ∧ 0 < ry ∧
      (sx + 1) * rx < 1 ∧ (sy + 1) * ry < 1 ∧
      Set.Ioo (-rx) rx ×ˢ Set.Ioo (-ry) ry ⊆ s := by
  rcases exists_centeredBox_subset_of_mem_nhds_zero hs with
    ⟨rx₀, ry₀, hrx₀, hry₀, hbox⟩
  let rx := min rx₀ (safeRadius sx)
  let ry := min ry₀ (safeRadius sy)
  have hrx : 0 < rx := lt_min hrx₀ (safeRadius_pos hsx)
  have hry : 0 < ry := lt_min hry₀ (safeRadius_pos hsy)
  refine ⟨rx, ry, hrx, hry, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (min_le_right rx₀ (safeRadius sx))
        (by linarith))
      (mul_safeRadius_lt_one hsx)
  · exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (min_le_right ry₀ (safeRadius sy))
        (by linarith))
      (mul_safeRadius_lt_one hsy)
  · intro z hz
    apply hbox
    constructor
    · have hx : |z.1| < rx := abs_lt.mpr hz.1
      exact abs_lt.mp (hx.trans_le (min_le_left rx₀ (safeRadius sx)))
    · have hy : |z.2| < ry := abs_lt.mpr hz.2
      exact abs_lt.mp (hy.trans_le (min_le_left ry₀ (safeRadius sy)))

end
end CKLocalBox
end StressTensor
