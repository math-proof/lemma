import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.WavefrontSetExtendedConvolution
open MeasureTheory Set ConeSupport
open scoped SchwartzMap FourierTransform


namespace ConeSupport

/--
[convolution_well_defined_lemma_12_6](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetExtendedConvolution.lean)
-/
@[path]
lemma convolution_well_defined_lemma_12_6
  {n : ℕ}
  {u : 𝓢'(E n, ℂ)}
  {C : ConvolutionSystem n}
  {d₁ d₂ : SchwartzCompactDecomp u}
-- given
  (hu : ConicSingularSupportSphere u = ∅) :
-- imply
  C.convSchwartz d₁.schwartzPart + C.convCompact d₁.compactPart = C.convSchwartz d₂.schwartzPart + C.convCompact d₂.compactPart :=
-- proof
  convolution_decomp_well_defined
    (hasEmptyConicSingularSupportSphere_of_eq_empty u hu) C d₁ d₂

end ConeSupport


-- created on 2026-10-23
