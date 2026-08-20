import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Analytic uniqueness from the full Taylor jet

This file isolates the final identity-theorem step used in a power-series
proof of Cauchy--Kowalevskaya.  An analytic germ whose iterated Frechet
derivatives all vanish is locally zero.  Consequently two analytic germs
with the same full Taylor jet agree in a neighborhood of the base point.

The result is valid for arbitrary real normed spaces and does not assume a
one-dimensional domain.
-/

namespace StressTensor

noncomputable section

open Filter

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- An analytic germ with vanishing iterated Frechet derivatives of every
order is identically zero on some neighborhood of its center. -/
theorem AnalyticAt.eventuallyEq_zero_of_iteratedFDeriv_eq_zero
    {f : E → F} {x : E} (hf : AnalyticAt ℝ f x)
    (hjet : ∀ n : ℕ, iteratedFDeriv ℝ n f x = 0) :
    f =ᶠ[nhds x] 0 := by
  rcases hf with ⟨p, r, hp⟩
  have hdiag : ∀ (n : ℕ) (y : E), p n (fun _ : Fin n => y) = 0 := by
    intro n y
    have hformula := hp.iteratedFDeriv_eq_sum_of_completeSpace
      (n := n) (fun _ : Fin n => y)
    rw [hjet n] at hformula
    simp only [zero_apply] at hformula
    have hsum :
        (∑ _σ : Equiv.Perm (Fin n), p n (fun _ : Fin n => y)) = 0 := by
      simpa using hformula.symm
    have hmultiple : n.factorial • p n (fun _ : Fin n => y) = 0 := by
      simpa [Fintype.card_perm, Fintype.card_fin] using hsum
    have hscalar : (n.factorial : ℝ) • p n (fun _ : Fin n => y) = 0 := by
      simpa only [Nat.cast_smul_eq_nsmul] using hmultiple
    exact (smul_eq_zero.mp hscalar).resolve_left (by
      exact_mod_cast Nat.factorial_ne_zero n)
  filter_upwards [hp.eventually_hasSum_sub] with z hz
  have hz0 : HasSum (fun n : ℕ => p n (fun _ : Fin n => z - x)) 0 := by
    convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : F)) 0) using 1
    funext n
    exact hdiag n (z - x)
  exact hz.unique hz0

/-- Two analytic germs with identical iterated Frechet derivatives agree on
some neighborhood of the base point. -/
theorem AnalyticAt.eventuallyEq_of_iteratedFDeriv_eq
    {f g : E → F} {x : E} (hf : AnalyticAt ℝ f x)
    (hg : AnalyticAt ℝ g x)
    (hjet : ∀ n : ℕ, iteratedFDeriv ℝ n f x = iteratedFDeriv ℝ n g x) :
    f =ᶠ[nhds x] g := by
  have hsub : AnalyticAt ℝ (f - g) x := hf.sub hg
  have hzero : ∀ n : ℕ, iteratedFDeriv ℝ n (f - g) x = 0 := by
    intro n
    have hfcont : ContDiffAt ℝ n f x := hf.contDiffAt
    have hgcont : ContDiffAt ℝ n g x := hg.contDiffAt
    ext v
    rw [iteratedFDeriv_sub_apply hfcont hgcont, hjet n]
    simp
  have hevent :=
    AnalyticAt.eventuallyEq_zero_of_iteratedFDeriv_eq_zero hsub hzero
  filter_upwards [hevent] with z hz
  exact sub_eq_zero.mp hz

/-- On a preconnected analytic domain, equality of the full Taylor jet at
one point propagates to equality throughout the domain. -/
theorem AnalyticOnNhd.eqOn_of_iteratedFDeriv_eq
    {f g : E → F} {U : Set E} {x : E}
    (hf : AnalyticOnNhd ℝ f U) (hg : AnalyticOnNhd ℝ g U)
    (hU : IsPreconnected U) (hx : x ∈ U)
    (hjet : ∀ n : ℕ,
      iteratedFDeriv ℝ n f x = iteratedFDeriv ℝ n g x) :
    Set.EqOn f g U := by
  have hlocal := AnalyticAt.eventuallyEq_of_iteratedFDeriv_eq
    (hf x hx) (hg x hx) hjet
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hU hx hlocal

end

end StressTensor
