import Theorem31Packaging
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Dense extension of the weak Euler identity

This module is separate from `Section33WeakEuler` because the concrete
Sobolev test structure is declared in `Theorem31Packaging`.  The passage from
smooth tests is an ordinary dominated-convergence argument against the
localized integrable stress.
-/

open Filter MeasureTheory Set Topology

noncomputable section

namespace Theorem31

open GammaMaximalityBridge MaximalityOfU StressTensor

namespace W11ZeroW1InfinityTest

/-- Each member of the recorded smooth approximation sequence is a
`SmoothTest`; the topological-support condition is stronger than the support
condition required there. -/
def smoothTest {ell : ℝ} (phi : W11ZeroW1InfinityTest ell) (n : ℕ) :
    SmoothTest ell where
  toFun := phi.approximation n
  contDiff := (phi.approximation_smooth n).of_le le_top
  support_subset :=
    (subset_tsupport (phi.approximation n)).trans
      (phi.approximation_support n)

@[simp] theorem smoothTest_apply {ell : ℝ}
    (phi : W11ZeroW1InfinityTest ell) (n : ℕ) (z : Plane) :
    phi.smoothTest n z = phi.approximation n z := rfl

@[simp] theorem classicalGradient_smoothTest {ell : ℝ}
    (phi : W11ZeroW1InfinityTest ell) (n : ℕ) :
    classicalGradient (phi.smoothTest n) =
      classicalGradient (phi.approximation n) := rfl

end W11ZeroW1InfinityTest

set_option maxHeartbeats 1000000 in
/-- Dominated-convergence extension of the smooth weak Euler equation to the
concrete density presentation of `W¹₀,¹ ∩ W¹,∞`.

The assumptions are minimal at this level: `K` supplies analyticity and the
PDE, `L` supplies the compact localization and integrable stress estimate,
and `phi` itself records the a.e. gradient convergence and common `L∞` bound.
-/
theorem dense_weakEuler
    {P : Params} {U : Set Plane} {r : ℝ}
    (K : CKOutcome P U r) (L : CompactSquareLocalization P K.gamma U)
    (phi : W11ZeroW1InfinityTest L.ell) :
    (∫ z in cube L.ell,
      inner ℝ (stressField P K.gamma z) (phi.map.gradient z)) = 0 := by
  let mu : Measure Plane := volume.restrict (cube L.ell)
  let F : ℕ → Plane → ℝ := fun n z =>
    inner ℝ (stressField P K.gamma z)
      (classicalGradient (phi.approximation n) z)
  let target : Plane → ℝ := fun z =>
    inner ℝ (stressField P K.gamma z) (phi.map.gradient z)
  have hs : Integrable (stressField P K.gamma) mu := by
    change IntegrableOn (stressField P K.gamma) (cube L.ell) volume
    exact localized_stressField_integrableOn_cube L K.solution.1
  obtain ⟨M, hMnonneg, hM⟩ := phi.gradient_uniformly_bounded
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) mu := by
    intro n
    have hsmooth := integrableOn_inner_stressField_classicalGradient
      K L (phi.smoothTest n)
    exact hsmooth.aestronglyMeasurable
  have hmajor : Integrable
      (fun z => M * ‖stressField P K.gamma z‖) mu :=
    hs.norm.const_mul M
  have hbound : ∀ n, ∀ᵐ z ∂mu,
      ‖F n z‖ ≤ M * ‖stressField P K.gamma z‖ := by
    intro n
    filter_upwards [hM n] with z hz
    calc
      ‖F n z‖ ≤
          ‖stressField P K.gamma z‖ *
            ‖classicalGradient (phi.approximation n) z‖ := by
        exact norm_inner_le_norm _ _
      _ ≤ ‖stressField P K.gamma z‖ * M :=
        mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ = M * ‖stressField P K.gamma z‖ := mul_comm _ _
  have hlimit : ∀ᵐ z ∂mu,
      Tendsto (fun n => F n z) atTop (𝓝 (target z)) := by
    filter_upwards [phi.gradient_tendsto_ae] with z hz
    simpa only [F, target] using
      (tendsto_const_nhds.inner hz :
        Tendsto
          (fun n => inner ℝ (stressField P K.gamma z)
            (classicalGradient (phi.approximation n) z))
          atTop
          (𝓝 (inner ℝ (stressField P K.gamma z)
            (phi.map.gradient z))))
  have hDCT : Tendsto (fun n => ∫ z, F n z ∂mu) atTop
      (𝓝 (∫ z, target z ∂mu)) :=
    tendsto_integral_of_dominated_convergence
      (fun z => M * ‖stressField P K.gamma z‖)
      hFmeas hmajor hbound hlimit
  have hzero : Tendsto (fun n => ∫ z, F n z ∂mu) atTop (𝓝 0) := by
    have heach : ∀ n, (∫ z, F n z ∂mu) = 0 := by
      intro n
      change (∫ z in cube L.ell,
        inner ℝ (stressField P K.gamma z)
          (classicalGradient (phi.smoothTest n) z)) = 0
      exact smooth_weakEuler K L (phi.smoothTest n)
    simpa only [heach] using (tendsto_const_nhds :
      Tendsto (fun _n : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have htarget : (∫ z, target z ∂mu) = 0 :=
    tendsto_nhds_unique hDCT hzero
  exact htarget

/-- Method-style spelling of `dense_weakEuler`. -/
theorem CKOutcome.weakEuler_dense
    {P : Params} {U : Set Plane} {r : ℝ}
    (K : CKOutcome P U r) (L : CompactSquareLocalization P K.gamma U)
    (phi : W11ZeroW1InfinityTest L.ell) :
    (∫ z in cube L.ell,
      inner ℝ (stressField P K.gamma z) (phi.map.gradient z)) = 0 :=
  dense_weakEuler K L phi

end Theorem31
