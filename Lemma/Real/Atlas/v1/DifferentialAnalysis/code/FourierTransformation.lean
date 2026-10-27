import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.DifferentialAnalysis.code.FourierTransformation
open MeasureTheory SchwartzMap FourierTransformation
open scoped FourierTransform ComplexInnerProductSpace


namespace FourierTransformation

/--
[fourier_continuousLinearMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierTransformation.lean)
-/
@[path]
lemma fourier_continuousLinearMap
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  [NormedAddCommGroup F]
  [InnerProductSpace ℂ F] :
-- imply
  ∃ T : 𝓢(V, F) →L[ℂ] 𝓢(V, F), ∀ f : 𝓢(V, F), T f = 𝓕 f :=
-- proof
  ⟨SchwartzMap.fourierTransformCLM ℂ, fun _ => rfl⟩
end FourierTransformation



-- created on 2026-10-23
