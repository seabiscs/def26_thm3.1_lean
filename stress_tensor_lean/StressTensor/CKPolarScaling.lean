import StressTensor.CKPolarEvaluation

/-!
# Polar coefficients along two directions and exact rate scaling

The normalized majorant is constructed on an `L¹` product space, whereas
the formal recurrence is written on the ordinary `(x,y)` product.  Polar
coefficients only depend on two chosen directions.  This module shows that
continuous-linear reparametrization and separate rescaling of those
directions restore exactly the factor `R^m S^n`.
-/

namespace StressTensor
namespace CKPolarScaling

open scoped BigOperators

noncomputable section

/-- Put `ex` in the selected slots and `ey` in the complementary slots. -/
def polarSlotInputAlong
    {E : Type*} (ex ey : E) (k : ℕ) (s : Finset (Fin k)) : Fin k → E :=
  fun i => if i ∈ s then ex else ey

/-- Polar coefficient of an FMS along two arbitrary input directions. -/
def polarCoefficientAlong
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p : FormalMultilinearSeries ℝ E G) (ex ey : E) (m n : ℕ) : G :=
  ∑ s ∈ (Finset.univ : Finset (Fin (m + n))).powersetCard m,
    p (m + n) (polarSlotInputAlong ex ey (m + n) s)

theorem map_piecewise_smul_polarSlotInputAlong
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (q : E [×k]→L[ℝ] G) (s : Finset (Fin k))
    (ex ey : E) (x y : ℝ) :
    q (s.piecewise (fun _ => x • ex) (fun _ => y • ey)) =
      (x ^ s.card * y ^ (k - s.card)) •
        q (polarSlotInputAlong ex ey k s) := by
  have hinput :
      s.piecewise (fun _ => x • ex) (fun _ => y • ey) =
        fun i => (if i ∈ s then x else y) •
          polarSlotInputAlong ex ey k s i := by
    funext i
    by_cases hi : i ∈ s <;>
      simp [Finset.piecewise, polarSlotInputAlong, hi]
  rw [hinput, q.map_smul_univ]
  congr 1
  calc
    (∏ i : Fin k, if i ∈ s then x else y) =
        (∏ _i ∈ s, x) * ∏ _i ∈ sᶜ, y := by
      rw [Finset.prod_ite]
      congr 1
      · apply Finset.prod_congr
        · ext i
          simp
        · intro i hi
          rfl
      · apply Finset.prod_congr
        · ext i
          simp
        · intro i hi
          rfl
    _ = x ^ s.card * y ^ (k - s.card) := by
      simp only [Finset.prod_const, Finset.card_compl, Fintype.card_fin]

/-- Diagonal evaluation in the plane spanned by `ex,ey` is the polynomial
whose coefficients are `polarCoefficientAlong`. -/
theorem apply_diag_eq_sum_polarCoefficientAlong
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p : FormalMultilinearSeries ℝ E G)
    (k : ℕ) (ex ey : E) (x y : ℝ) :
    p k (fun _ => x • ex + y • ey) =
      ∑ m ∈ Finset.range (k + 1),
        (x ^ m * y ^ (k - m)) •
          polarCoefficientAlong p ex ey m (k - m) := by
  have hdiag : (fun _ : Fin k => x • ex + y • ey) =
      (fun _ => x • ex) + (fun _ => y • ey) := by
    funext i
    rfl
  rw [hdiag, (p k).map_add_univ]
  calc
    (∑ s : Finset (Fin k),
        p k (s.piecewise (fun _ => x • ex) (fun _ => y • ey))) =
      ∑ s : Finset (Fin k),
        (x ^ s.card * y ^ (k - s.card)) •
          p k (polarSlotInputAlong ex ey k s) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact map_piecewise_smul_polarSlotInputAlong (p k) s ex ey x y
    _ = ∑ m ∈ Finset.range (k + 1),
        ∑ s ∈ (Finset.univ : Finset (Fin k)).powersetCard m,
          (x ^ s.card * y ^ (k - s.card)) •
            p k (polarSlotInputAlong ex ey k s) := by
      symm
      have hmaps : ∀ s ∈ (Finset.univ : Finset (Finset (Fin k))),
          s.card ∈ Finset.range (k + 1) := by
        intro s hs
        simp only [Finset.mem_range]
        exact Nat.lt_succ_of_le (by simpa using Finset.card_le_univ s)
      simp_rw [Finset.powersetCard_eq_filter, Finset.powerset_univ]
      rw [Finset.sum_fiberwise_of_maps_to hmaps]
    _ = ∑ m ∈ Finset.range (k + 1),
        (x ^ m * y ^ (k - m)) •
          polarCoefficientAlong p ex ey m (k - m) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmk : m ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
      rw [polarCoefficientAlong, Nat.add_sub_of_le hmk]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [(Finset.mem_powersetCard.mp hs).2]

/-- Polarization commutes exactly with a continuous-linear change of input
variables. -/
theorem polarCoefficientAlong_compContinuousLinearMap
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p : FormalMultilinearSeries ℝ F G) (L : E →L[ℝ] F)
    (ex ey : E) (m n : ℕ) :
    polarCoefficientAlong (p.compContinuousLinearMap L) ex ey m n =
      polarCoefficientAlong p (L ex) (L ey) m n := by
  unfold polarCoefficientAlong
  apply Finset.sum_congr rfl
  intro s hs
  simp only [FormalMultilinearSeries.compContinuousLinearMap_apply]
  congr 1
  funext i
  simp only [Function.comp_apply, polarSlotInputAlong]
  split_ifs <;> rfl

/-- Scaling the two polar directions multiplies the `(m,n)` coefficient by
`R^m S^n`, with no loss. -/
theorem polarCoefficientAlong_smul_directions
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p : FormalMultilinearSeries ℝ E G)
    (ex ey : E) (R S : ℝ) (m n : ℕ) :
    polarCoefficientAlong p (R • ex) (S • ey) m n =
      (R ^ m * S ^ n) • polarCoefficientAlong p ex ey m n := by
  unfold polarCoefficientAlong
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hcard : s.card = m := (Finset.mem_powersetCard.mp hs).2
  have hmap := map_piecewise_smul_polarSlotInputAlong
    (p (m + n)) s ex ey R S
  have hpiece :
      s.piecewise (fun _ => R • ex) (fun _ => S • ey) =
        polarSlotInputAlong (R • ex) (S • ey) (m + n) s := by
    funext i
    by_cases hi : i ∈ s <;>
      simp [Finset.piecewise, polarSlotInputAlong, hi]
  rw [hpiece, hcard, Nat.add_sub_cancel_left] at hmap
  exact hmap

/-- Unit polar directions cost only the binomial number of subsets. -/
theorem norm_polarCoefficientAlong_le
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p : FormalMultilinearSeries ℝ E G) (ex ey : E)
    (hex : ‖ex‖ ≤ 1) (hey : ‖ey‖ ≤ 1) (m n : ℕ) :
    ‖polarCoefficientAlong p ex ey m n‖ ≤
      ((m + n).choose m : ℝ) * ‖p (m + n)‖ := by
  unfold polarCoefficientAlong
  calc
    ‖∑ s ∈ (Finset.univ : Finset (Fin (m + n))).powersetCard m,
        p (m + n) (polarSlotInputAlong ex ey (m + n) s)‖ ≤
      ∑ s ∈ (Finset.univ : Finset (Fin (m + n))).powersetCard m,
        ‖p (m + n) (polarSlotInputAlong ex ey (m + n) s)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _s ∈ (Finset.univ : Finset (Fin (m + n))).powersetCard m,
        ‖p (m + n)‖ := by
      apply Finset.sum_le_sum
      intro s hs
      calc
        ‖p (m + n) (polarSlotInputAlong ex ey (m + n) s)‖ ≤
            ‖p (m + n)‖ *
              ∏ i, ‖polarSlotInputAlong ex ey (m + n) s i‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
        _ ≤ ‖p (m + n)‖ * 1 := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          calc
            ∏ i, ‖polarSlotInputAlong ex ey (m + n) s i‖ ≤
                ∏ _i : Fin (m + n), (1 : ℝ) := by
              apply Finset.prod_le_prod
              · intro i hi
                exact norm_nonneg _
              · intro i hi
                unfold polarSlotInputAlong
                split_ifs
                · exact hex
                · exact hey
            _ = 1 := by simp
        _ = ‖p (m + n)‖ := mul_one _
    _ = ((m + n).choose m : ℝ) * ‖p (m + n)‖ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp

/-- The project-wide polar coefficient on `ℝ × ℝ` is the specialization
of `polarCoefficientAlong` to the two coordinate directions. -/
theorem polarCoefficientAlong_coordinateDirections
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p : FormalMultilinearSeries ℝ (ℝ × ℝ) G) (m n : ℕ) :
    polarCoefficientAlong p (1, 0) (0, 1) m n =
      CKPolarEvaluation.polarCoefficient p m n := by
  rfl

end
end CKPolarScaling
end StressTensor
