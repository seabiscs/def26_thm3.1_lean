import StressTensor.CKAnalyticMajorant
import StressTensor.CKNagumoMajorant
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

/-!
# Nagumo bounds for formal multilinear-series composition

This file proves that Mathlib's formal composition preserves the normalized
one-variable Nagumo coefficient bound.  If the positive-degree coefficients
of the inner series are bounded by

`epsilon * nagumoCoeff n * T ^ n`

and the outer coefficients by `A * r ^ l`, then, provided
`8 * (epsilon * r) < 1`, every positive coefficient of the composite is
bounded at the *same* scale `T`.  The loss is the explicit geometric factor
`(1 - 8 * (epsilon * r))^{-1}`.

This is deliberately a total-degree statement.  It assumes that a
one-variable formal multilinear-series estimate has already been obtained;
by itself it does not preserve two independent anisotropic bivariate rates.
-/

namespace StressTensor
namespace CKFMSNagumoComposition

open CKDiagonalMajorant CKNagumoMajorant FormalMultilinearSeries
open scoped BigOperators

noncomputable section

/-! ## Ordered tuples and iterated Cauchy convolution -/

/-- Sum of products of `u` over all ordered `l`-tuples of nonnegative
integers with total `n`. -/
def tupleConvolution (u : ℕ → ℝ) (l n : ℕ) : ℝ :=
  ∑ f ∈ Finset.Nat.antidiagonalTuple l n, ∏ i, u (f i)

/-- Adding one coordinate to an antidiagonal tuple performs one Cauchy
convolution. -/
theorem tupleConvolution_succ (u : ℕ → ℝ) (l n : ℕ) :
    tupleConvolution u (l + 1) n =
      ∑ ij ∈ Finset.antidiagonal n,
        u ij.1 * tupleConvolution u l ij.2 := by
  unfold tupleConvolution Finset.Nat.antidiagonalTuple
    Multiset.Nat.antidiagonalTuple
  simp only [List.Nat.antidiagonalTuple]
  change
    (List.map (fun f : Fin (l + 1) → ℕ => ∏ i, u (f i))
      (List.flatMap (fun ni : ℕ × ℕ =>
        (List.Nat.antidiagonalTuple l ni.2).map (Fin.cons ni.1))
        (List.Nat.antidiagonal n))).sum =
    (List.map (fun ij : ℕ × ℕ =>
      u ij.1 * (List.map (fun f : Fin l → ℕ => ∏ i, u (f i))
        (List.Nat.antidiagonalTuple l ij.2)).sum)
      (List.Nat.antidiagonal n)).sum
  generalize List.Nat.antidiagonal n = L
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, ih]
      congr 1
      simpa [Function.comp_def, Fin.prod_univ_succ] using
        List.sum_map_mul_left (List.Nat.antidiagonalTuple l a.2)
          (fun f : Fin l → ℕ => ∏ i, u (f i)) (u a.1)

/-- Scalar Cauchy convolution is commutative. -/
theorem convolution_comm (u v : ℕ → ℝ) (n : ℕ) :
    convolution u v n = convolution v u n := by
  unfold convolution
  calc
    ∑ ij ∈ Finset.antidiagonal n, u ij.1 * v ij.2 =
        ∑ ij ∈ (Finset.antidiagonal n).map
          (Equiv.prodComm ℕ ℕ).toEmbedding, v ij.1 * u ij.2 := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro ij hij
      simp [mul_comm]
    _ = ∑ ij ∈ Finset.antidiagonal n, v ij.1 * u ij.2 := by
      rw [Finset.HasAntidiagonal.map_prodComm_antidiagonal]

/-- An `(k+1)`-tuple product sum is exactly the `k`-fold convolution used by
the scalar Nagumo module. -/
theorem tupleConvolution_eq_iteratedConvolution
    (u : ℕ → ℝ) (k n : ℕ) :
    tupleConvolution u (k + 1) n = iteratedConvolution u k n := by
  induction k generalizing n with
  | zero => simp [tupleConvolution]
  | succ k ih =>
      rw [tupleConvolution_succ]
      simp_rw [ih]
      change convolution u (iteratedConvolution u k) n =
        convolution (iteratedConvolution u k) u n
      exact convolution_comm _ _ _

/-! ## Reindexing positive compositions -/

/-- Scalar weight attached to an ordered composition.  It is written using
the block list so that Mathlib's composition change-of-variables theorem can
reduce it definitionally to an ordered tuple product. -/
def compositionWeight (u : ℕ → ℝ) (theta : ℝ)
    {m : ℕ} (c : Composition m) : ℝ :=
  theta ^ c.blocks.length * (c.blocks.map u).prod

private theorem compChangeOfVariables_weight
    (u : ℕ → ℝ) (theta : ℝ) (n : ℕ)
    (e : Σ l : ℕ, Fin l → ℕ)
    (he : e ∈ compPartialSumSource 1 (n + 1) (n + 1)) :
    (if ∑ i, e.2 i = n then
        theta ^ e.1 * ∏ i, u (e.2 i) else 0) =
      (if (compChangeOfVariables 1 (n + 1) (n + 1) e he).1 = n then
        compositionWeight u theta
          (compChangeOfVariables 1 (n + 1) (n + 1) e he).2 else 0) := by
  rcases e with ⟨l, f⟩
  dsimp [compChangeOfVariables, compositionWeight]
  congr 1
  simp [List.prod_ofFn]

private def sigmaCompositionEmbedding (n : ℕ) :
    Composition n ↪ (Σ m, Composition m) where
  toFun c := ⟨n, c⟩
  inj' := by intro a b h; cases h; rfl

private theorem target_indicator_eq
    (u : ℕ → ℝ) (theta : ℝ) {n : ℕ} (hn : 0 < n) :
    ∑ a ∈ compPartialSumTarget 1 (n + 1) (n + 1),
      (if a.1 = n then compositionWeight u theta a.2 else 0) =
        ∑ c : Composition n, compositionWeight u theta c := by
  rw [← Finset.sum_filter]
  have hfilter :
      (compPartialSumTarget 1 (n + 1) (n + 1)).filter
          (fun a => a.1 = n) =
        (Finset.univ : Finset (Composition n)).map
          (sigmaCompositionEmbedding n) := by
    ext a
    rcases a with ⟨m, c⟩
    by_cases hmn : m = n
    · subst m
      simp only [Finset.mem_filter, mem_compPartialSumTarget_iff,
        Finset.mem_map, Finset.mem_univ, true_and,
        sigmaCompositionEmbedding]
      constructor
      · intro h
        exact ⟨c, rfl⟩
      · rintro ⟨d, hd⟩
        cases hd
        exact ⟨⟨c.length_pos_of_pos hn, Nat.lt_succ_of_le c.length_le,
          fun j => Nat.lt_succ_of_le (c.blocksFun_le j)⟩, trivial⟩
    · simp only [Finset.mem_filter, hmn, and_false, Finset.mem_map,
        Finset.mem_univ, true_and]
      constructor
      · intro h; contradiction
      · rintro ⟨d, hd⟩
        exact (hmn (congrArg Sigma.fst hd).symm).elim
  rw [hfilter, Finset.sum_map]
  rfl

private theorem source_indicator_le
    (u : ℕ → ℝ) (theta : ℝ) (n : ℕ)
    (htheta : 0 ≤ theta) (hu : ∀ j, 0 ≤ u j) :
    ∑ e ∈ compPartialSumSource 1 (n + 1) (n + 1),
      (if ∑ i, e.2 i = n then
        theta ^ e.1 * ∏ i, u (e.2 i) else 0) ≤
        ∑ l ∈ Finset.Ico 1 (n + 1),
          theta ^ l * tupleConvolution u l n := by
  rw [compPartialSumSource, Finset.sum_sigma]
  apply Finset.sum_le_sum
  intro l hl
  rw [← Finset.sum_filter]
  calc
    ∑ f ∈ (Fintype.piFinset fun _i : Fin l =>
          Finset.Ico 1 (n + 1)).filter (fun f => ∑ i, f i = n),
        theta ^ l * ∏ i, u (f i) ≤
      ∑ f ∈ Finset.Nat.antidiagonalTuple l n,
        theta ^ l * ∏ i, u (f i) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro f hf
        rw [Finset.mem_filter] at hf
        exact Finset.Nat.mem_antidiagonalTuple.mpr hf.2
      · intro f hf hnot
        exact mul_nonneg (pow_nonneg htheta _)
          (Finset.prod_nonneg fun i hi => hu _)
    _ = theta ^ l * tupleConvolution u l n := by
      unfold tupleConvolution
      rw [Finset.mul_sum]

/-- The sum of Nagumo weights over every ordered composition of a positive
degree is bounded by a geometric series. -/
theorem sum_compositionWeight_le
    (u : ℕ → ℝ) (theta : ℝ) {n : ℕ}
    (hn : 0 < n) (htheta : 0 ≤ theta) (hu : ∀ j, 0 ≤ u j) :
    ∑ c : Composition n, compositionWeight u theta c ≤
      ∑ l ∈ Finset.Ico 1 (n + 1),
        theta ^ l * tupleConvolution u l n := by
  calc
    ∑ c : Composition n, compositionWeight u theta c =
        ∑ a ∈ compPartialSumTarget 1 (n + 1) (n + 1),
          (if a.1 = n then compositionWeight u theta a.2 else 0) :=
      (target_indicator_eq u theta hn).symm
    _ = ∑ e ∈ compPartialSumSource 1 (n + 1) (n + 1),
          (if ∑ i, e.2 i = n then
            theta ^ e.1 * ∏ i, u (e.2 i) else 0) := by
      symm
      exact compChangeOfVariables_sum 1 (n + 1) (n + 1) _ _
        (compChangeOfVariables_weight u theta n)
    _ ≤ ∑ l ∈ Finset.Ico 1 (n + 1),
          theta ^ l * tupleConvolution u l n :=
      source_indicator_le u theta n htheta hu

/-- Closed Nagumo estimate for the full ordered-composition sum. -/
theorem sum_nagumoCompositionWeight_le
    {theta : ℝ} {n : ℕ} (hn : 0 < n)
    (htheta : 0 ≤ theta) (hsmall : 8 * theta < 1) :
    ∑ c : Composition n,
        compositionWeight nagumoCoeff theta c ≤
      theta / (1 - 8 * theta) * nagumoCoeff n := by
  calc
    ∑ c : Composition n, compositionWeight nagumoCoeff theta c ≤
        ∑ l ∈ Finset.Ico 1 (n + 1),
          theta ^ l * tupleConvolution nagumoCoeff l n :=
      sum_compositionWeight_le nagumoCoeff theta hn htheta
        nagumoCoeff_nonneg
    _ ≤ ∑ l ∈ Finset.Ico 1 (n + 1),
          theta ^ l * ((8 : ℝ) ^ (l - 1) * nagumoCoeff n) := by
      apply Finset.sum_le_sum
      intro l hl
      have hlpos : 0 < l := (Finset.mem_Ico.mp hl).1
      have hleq : l - 1 + 1 = l := Nat.succ_pred_eq_of_pos hlpos
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg htheta _)
      calc
        tupleConvolution nagumoCoeff l n =
            tupleConvolution nagumoCoeff ((l - 1) + 1) n := by rw [hleq]
        _ = iteratedConvolution nagumoCoeff (l - 1) n :=
          tupleConvolution_eq_iteratedConvolution nagumoCoeff (l - 1) n
        _ ≤ (8 : ℝ) ^ (l - 1) * nagumoCoeff n :=
          iteratedConvolution_nagumoCoeff_le (l - 1) n
    _ = theta * nagumoCoeff n *
          (∑ k ∈ Finset.range n, (8 * theta) ^ k) := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_left]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [add_comm 1 k, pow_succ, mul_pow]
      ring
    _ ≤ theta * nagumoCoeff n * (1 / (1 - 8 * theta)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa using (geom_sum_Ico_le_of_lt_one
          (m := 0) (n := n) (mul_nonneg (by norm_num) htheta) hsmall)
      · exact mul_nonneg htheta (nagumoCoeff_nonneg n)
    _ = theta / (1 - 8 * theta) * nagumoCoeff n := by ring

/-! ## Formal multilinear-series bounds -/

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Product estimate for the inner coefficients along the blocks of one
ordered composition. -/
theorem prod_inner_nagumo_bound
    {p : FormalMultilinearSeries ℝ E F} {epsilon T : ℝ}
    (_hepsilon : 0 ≤ epsilon) (_hT : 0 ≤ T)
    (hp : ∀ k, 0 < k →
      ‖p k‖ ≤ epsilon * nagumoCoeff k * T ^ k)
    {n : ℕ} (c : Composition n) :
    ∏ i, ‖p (c.blocksFun i)‖ ≤
      epsilon ^ c.length * (∏ i, nagumoCoeff (c.blocksFun i)) * T ^ n := by
  calc
    ∏ i, ‖p (c.blocksFun i)‖ ≤
        ∏ i, epsilon * nagumoCoeff (c.blocksFun i) *
          T ^ (c.blocksFun i) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact norm_nonneg _
      · intro i hi
        exact hp _ (c.one_le_blocksFun i)
    _ = epsilon ^ c.length *
          (∏ i, nagumoCoeff (c.blocksFun i)) * T ^ n := by
      simp_rw [mul_assoc]
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Finset.prod_pow_eq_pow_sum, c.sum_blocksFun]

/-- Norm estimate for one ordered-composition summand. -/
theorem compAlongComposition_norm_le_nagumo
    {q : FormalMultilinearSeries ℝ F G}
    {p : FormalMultilinearSeries ℝ E F}
    {A r epsilon T : ℝ}
    (hA : 0 ≤ A) (hr : 0 ≤ r)
    (hepsilon : 0 ≤ epsilon) (hT : 0 ≤ T)
    (hq : ∀ l, ‖q l‖ ≤ A * r ^ l)
    (hp : ∀ k, 0 < k →
      ‖p k‖ ≤ epsilon * nagumoCoeff k * T ^ k)
    {n : ℕ} (c : Composition n) :
    ‖q.compAlongComposition p c‖ ≤
      A * T ^ n * compositionWeight nagumoCoeff (epsilon * r) c := by
  have hprod := prod_inner_nagumo_bound hepsilon hT hp c
  calc
    ‖q.compAlongComposition p c‖ ≤
        ‖q c.length‖ * ∏ i, ‖p (c.blocksFun i)‖ :=
      q.compAlongComposition_norm p c
    _ ≤ (A * r ^ c.length) *
        (epsilon ^ c.length *
          (∏ i, nagumoCoeff (c.blocksFun i)) * T ^ n) := by
      exact mul_le_mul (hq c.length) hprod
        (Finset.prod_nonneg fun _ _ => norm_nonneg _)
        (mul_nonneg hA (pow_nonneg hr _))
    _ = A * T ^ n * compositionWeight nagumoCoeff (epsilon * r) c := by
      unfold compositionWeight
      rw [show (c.blocks.map nagumoCoeff).prod =
          ∏ i, nagumoCoeff (c.blocksFun i) by
        rw [← c.ofFn_blocksFun, List.map_ofFn, List.prod_ofFn]
        rfl]
      rw [mul_pow]
      ring

/-- Nagumo-stable composition estimate at the same homogeneous scale `T`.
The assumption `p 0 = 0` records the usual centered-series hypothesis;
Mathlib's `comp` ignores that coefficient by construction. -/
theorem norm_comp_le_nagumo
    {q : FormalMultilinearSeries ℝ F G}
    {p : FormalMultilinearSeries ℝ E F}
    {A r epsilon T : ℝ}
    (hA : 0 ≤ A) (hr : 0 ≤ r)
    (hepsilon : 0 ≤ epsilon) (hT : 0 ≤ T)
    (hsmall : 8 * (epsilon * r) < 1)
    (hq : ∀ l, ‖q l‖ ≤ A * r ^ l)
    (_hp0 : p 0 = 0)
    (hp : ∀ k, 0 < k →
      ‖p k‖ ≤ epsilon * nagumoCoeff k * T ^ k)
    {n : ℕ} (hn : 0 < n) :
    ‖q.comp p n‖ ≤
      A * ((epsilon * r) / (1 - 8 * (epsilon * r))) *
        nagumoCoeff n * T ^ n := by
  have htheta : 0 ≤ epsilon * r := mul_nonneg hepsilon hr
  calc
    ‖q.comp p n‖ =
        ‖∑ c : Composition n, q.compAlongComposition p c‖ := rfl
    _ ≤ ∑ c : Composition n, ‖q.compAlongComposition p c‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c : Composition n,
        A * T ^ n * compositionWeight nagumoCoeff (epsilon * r) c := by
      exact Finset.sum_le_sum fun c hc =>
        compAlongComposition_norm_le_nagumo hA hr hepsilon hT hq hp c
    _ = A * T ^ n *
        (∑ c : Composition n,
          compositionWeight nagumoCoeff (epsilon * r) c) := by
      rw [Finset.mul_sum]
    _ ≤ A * T ^ n *
        ((epsilon * r) / (1 - 8 * (epsilon * r)) * nagumoCoeff n) := by
      exact mul_le_mul_of_nonneg_left
        (sum_nagumoCompositionWeight_le hn htheta hsmall)
        (mul_nonneg hA (pow_nonneg hT _))
    _ = A * ((epsilon * r) / (1 - 8 * (epsilon * r))) *
        nagumoCoeff n * T ^ n := by ring

/-! ## Isolating the constant coefficient -/

/-- Formal series consisting only of a prescribed constant value. -/
def constantOnly (g : G) : FormalMultilinearSeries ℝ E G
  | 0 => ContinuousMultilinearMap.uncurry0 ℝ E g
  | _ + 1 => 0

@[simp] theorem constantOnly_zero (g : G) :
    constantOnly (E := E) g 0 =
      ContinuousMultilinearMap.uncurry0 ℝ E g := rfl

@[simp] theorem constantOnly_succ (g : G) (n : ℕ) :
    constantOnly (E := E) g (n + 1) = 0 := rfl

/-- Subtracting the transported outer constant coefficient is exactly
`removeZero` of the composite. -/
theorem comp_sub_constantOnly_eq_removeZero
    (q : FormalMultilinearSeries ℝ F G)
    (p : FormalMultilinearSeries ℝ E F) :
    q.comp p - constantOnly (E := E) (q 0).curry0 =
      (q.comp p).removeZero := by
  apply FormalMultilinearSeries.ext
  intro n
  cases n with
  | zero =>
      ext v
      change (q.comp p 0) v - (q 0).curry0 = 0
      rw [sub_eq_zero]
      exact q.comp_coeff_zero p v 0
  | succ n =>
      simp [constantOnly, FormalMultilinearSeries.removeZero]

/-- The positive-degree Nagumo estimate applies verbatim after the constant
coefficient has been removed. -/
theorem norm_comp_sub_constantOnly_le_nagumo
    {q : FormalMultilinearSeries ℝ F G}
    {p : FormalMultilinearSeries ℝ E F}
    {A r epsilon T : ℝ}
    (hA : 0 ≤ A) (hr : 0 ≤ r)
    (hepsilon : 0 ≤ epsilon) (hT : 0 ≤ T)
    (hsmall : 8 * (epsilon * r) < 1)
    (hq : ∀ l, ‖q l‖ ≤ A * r ^ l)
    (hp0 : p 0 = 0)
    (hp : ∀ k, 0 < k →
      ‖p k‖ ≤ epsilon * nagumoCoeff k * T ^ k)
    {n : ℕ} (hn : 0 < n) :
    ‖(q.comp p - constantOnly (E := E) (q 0).curry0) n‖ ≤
      A * ((epsilon * r) / (1 - 8 * (epsilon * r))) *
        nagumoCoeff n * T ^ n := by
  rw [comp_sub_constantOnly_eq_removeZero,
    FormalMultilinearSeries.removeZero_of_pos _ hn]
  exact norm_comp_le_nagumo hA hr hepsilon hT hsmall hq hp0 hp hn

/-! ## Packaged analytic-germ specialization -/

/-- Radius-form specialization for a packaged local analytic majorant. -/
theorem LocalAnalyticMajorant.norm_comp_le_nagumo
    {f : F → G} {x : F} (M : LocalAnalyticMajorant f x)
    {p : FormalMultilinearSeries ℝ E F} {epsilon T : ℝ}
    (hepsilon : 0 ≤ epsilon) (hT : 0 ≤ T)
    (hsmall : 8 * (epsilon * (M.radius : ℝ)⁻¹) < 1)
    (hp0 : p 0 = 0)
    (hp : ∀ k, 0 < k →
      ‖p k‖ ≤ epsilon * nagumoCoeff k * T ^ k)
    {n : ℕ} (hn : 0 < n) :
    ‖M.series.comp p n‖ ≤
      M.coefficientBound *
        ((epsilon * (M.radius : ℝ)⁻¹) /
          (1 - 8 * (epsilon * (M.radius : ℝ)⁻¹))) *
        nagumoCoeff n * T ^ n := by
  apply CKFMSNagumoComposition.norm_comp_le_nagumo
    M.coefficientBound_pos.le
    (inv_nonneg.mpr M.radius_real_pos.le) hepsilon hT hsmall _ hp0 hp hn
  intro l
  calc
    ‖M.series l‖ ≤ M.coefficientBound / (M.radius : ℝ) ^ l :=
      M.coeff_norm_le l
    _ = M.coefficientBound * ((M.radius : ℝ)⁻¹) ^ l := by
      rw [inv_pow]
      ring

end

end CKFMSNagumoComposition
end StressTensor
