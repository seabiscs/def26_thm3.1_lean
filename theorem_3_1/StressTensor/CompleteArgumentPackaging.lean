import StressTensor.CompleteArgument
import StressTensor.NormalFormAnalyticity

/-!
# Topological and exponent packaging for the complete argument

This module supplies two pieces of bookkeeping which are implicit in the
manuscript but useful at the public boundary of the formalization:

* the literal neighborhoods `U_q` and `V_q` are open in their standard
  finite-dimensional coordinate spaces; and
* every real exponent `p > 2` canonically determines the admissible Hölder
  pair `q = p / (p - 1)`, to which the complete argument applies.
-/

namespace StressTensor

noncomputable section

/-! ## Openness of the manuscript neighborhoods -/

/-- The seven-dimensional manuscript neighborhood `U_q`, viewed in the
standard coordinate space used by the Cauchy--Kowalevskaya normal form, is
open. -/
theorem isOpen_ckPhaseInU (P : Params) :
    IsOpen {v : CKPhase | CKPhaseInU P v} := by
  have hcoord (i : Fin 7) : Continuous (fun v : CKPhase => v i) :=
    continuous_apply i
  have hx : IsOpen {v : CKPhase | |v 0| < P.rho} :=
    isOpen_lt ((hcoord 0).abs) continuous_const
  have hy : IsOpen {v : CKPhase | |v 1| < P.rho} :=
    isOpen_lt ((hcoord 1).abs) continuous_const
  have hval : IsOpen {v : CKPhase | |v 2| < P.rho} :=
    isOpen_lt ((hcoord 2).abs) continuous_const
  have hdx : IsOpen {v : CKPhase | |v 3 + 1| < P.rho} :=
    isOpen_lt (((hcoord 3).add continuous_const).abs) continuous_const
  have hdy : IsOpen {v : CKPhase | |v 4| < P.rho} :=
    isOpen_lt ((hcoord 4).abs) continuous_const
  have hdxy : IsOpen {v : CKPhase | |v 5| < 1} :=
    isOpen_lt ((hcoord 5).abs) continuous_const
  have hdyy : IsOpen {v : CKPhase | |v 6| < 1} :=
    isOpen_lt ((hcoord 6).abs) continuous_const
  simpa only [CKPhaseInU, InU, InQ, ckPhaseJet, Set.ofPred_and] using
    (hx.inter hy).inter
      (hval.inter (hdx.inter (hdy.inter (hdxy.inter hdyy))))

/-- The scalar manuscript neighborhood `V_q` is open in `ℝ²`. -/
theorem isOpen_inV (P : Params) :
    IsOpen {z : ℝ × ℝ | InV P z.1 z.2} := by
  have ht : IsOpen {z : ℝ × ℝ | |z.1| < P.rho} :=
    isOpen_lt continuous_fst.abs continuous_const
  have hd : IsOpen {z : ℝ × ℝ | |z.2 + 2| < 4 * P.rho} :=
    isOpen_lt (continuous_snd.add continuous_const).abs continuous_const
  simpa only [InV, Set.ofPred_and] using ht.inter hd

/-! ## Canonical packaging of a manuscript exponent -/

namespace Params

/-- The admissible parameter package canonically associated to a manuscript
exponent `p > 2`, with Hölder conjugate `q = p / (p - 1)`. -/
noncomputable def ofExponent (p : ℝ) (hp : 2 < p) : Params where
  p := p
  q := p / (p - 1)
  one_lt_q := by
    apply (lt_div_iff₀ (by linarith : 0 < p - 1)).2
    linarith
  q_lt_two := by
    apply (div_lt_iff₀ (by linarith : 0 < p - 1)).2
    linarith
  two_lt_p := hp
  holder := by
    have hp0 : p ≠ 0 := by linarith
    have hpm1 : p - 1 ≠ 0 := by linarith
    field_simp [hp0, hpm1]
    ring

@[simp] theorem ofExponent_p (p : ℝ) (hp : 2 < p) :
    (ofExponent p hp).p = p := rfl

@[simp] theorem ofExponent_q (p : ℝ) (hp : 2 < p) :
    (ofExponent p hp).q = p / (p - 1) := rfl

end Params

/-- The complete package of conclusions produced by the formalized argument. -/
def CompleteArgumentConclusion (P : Params) : Prop :=
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
        K.gamma w.1 (-w.2) = K.gamma w.1 w.2)

/-- For every manuscript exponent `p > 2`, the canonical Hölder-conjugate
parameter package satisfies the complete formalized conclusion. -/
theorem exists_complete_argument_of_two_lt
    (p : ℝ) (hp : 2 < p) :
    CompleteArgumentConclusion (Params.ofExponent p hp) :=
  CompleteArgument.exists_complete_argument (Params.ofExponent p hp)

end

end StressTensor
