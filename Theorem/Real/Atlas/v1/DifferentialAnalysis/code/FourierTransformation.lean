module

public import Mathlib
public import Theorem.v1.Atlas.DifferentialAnalysis.code.FourierTransformation

public section

open MeasureTheory SchwartzMap FourierTransformation
open scoped FourierTransform ComplexInnerProductSpace


namespace FourierTransformation

/--
[fourier_continuousLinearMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierTransformation.lean)
-/
public theorem fourier_continuousLinearMap
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  [MeasurableSpace V]
  [BorelSpace V]
  [NormedAddCommGroup F]
  [InnerProductSpace ℂ F] :
-- imply
  ∃ T : 𝓢(V, F) →L[ℂ] 𝓢(V, F), ∀ f : 𝓢(V, F), T f = 𝓕 f :=
-- proof
  ⟨SchwartzMap.fourierTransformCLM ℂ, fun _ => rfl⟩
end FourierTransformation



-- created on 2026-10-23
-- updated on 2026-11-15
