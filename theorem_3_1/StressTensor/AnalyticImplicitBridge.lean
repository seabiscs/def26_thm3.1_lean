import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Analytic regularity for Mathlib's implicit function

Mathlib constructs `ImplicitFunctionData.implicitFunction` through the local
inverse theorem and proves its strict differentiability.  The analytic inverse
theorem already available in Mathlib also shows that this particular implicit
function is analytic when both defining maps are analytic.  This short bridge
records that consequence in directly usable form.

This is an algebraic implicit-function theorem on Banach spaces.  It does not
by itself provide a Cauchy--Kowalevskaya theorem for differential equations.
-/

namespace StressTensor

noncomputable section

open Filter

variable {𝕜 E F G : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]

/-- The implicit function selected by `ImplicitFunctionData` is analytic at
the base point whenever its left and right defining maps are analytic there. -/
theorem ImplicitFunctionData.analyticAt_implicitFunction
    (φ : ImplicitFunctionData 𝕜 E F G)
    (hleft : AnalyticAt 𝕜 φ.leftFun φ.pt)
    (hright : AnalyticAt 𝕜 φ.rightFun φ.pt) :
    AnalyticAt 𝕜
      (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt) := by
  let i : E ≃L[𝕜] F × G :=
    φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv
      φ.range_leftDeriv φ.range_rightDeriv φ.isCompl_ker
  have hprod : AnalyticAt 𝕜 φ.prodFun φ.pt := by
    change AnalyticAt 𝕜 (fun x => (φ.leftFun x, φ.rightFun x)) φ.pt
    exact hleft.prod hright
  have hderiv : fderiv 𝕜 φ.prodFun φ.pt = i := by
    exact φ.hasStrictFDerivAt.hasFDerivAt.fderiv
  have hinv : AnalyticAt 𝕜 φ.toOpenPartialHomeomorph.symm
      (φ.prodFun φ.pt) := by
    exact φ.toOpenPartialHomeomorph.analyticAt_symm'
      φ.pt_mem_toOpenPartialHomeomorph_source hprod hderiv
  have hinclude : AnalyticAt 𝕜
      (fun z : G => (φ.leftFun φ.pt, z)) (φ.rightFun φ.pt) := by
    exact analyticAt_const.prod analyticAt_id
  have hcomp := hinv.comp_of_eq hinclude (by rfl)
  apply hcomp.congr
  exact Filter.Eventually.of_forall fun z => rfl

end

end StressTensor
