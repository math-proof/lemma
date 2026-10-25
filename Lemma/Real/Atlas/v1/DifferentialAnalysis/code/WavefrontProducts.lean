import Mathlib
import sympy.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.WavefrontProducts.Part2
open MeasureTheory Set WavefrontSet


/--
[disjointWFscProduct_implies_disjointWFscConvolution_fourier](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontProducts.lean)
-/
@[path]
private lemma disjointWFscProduct_implies_disjointWFscConvolution_fourier_eq
  {n : ℕ}
  {u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hcond : DisjointWFscProductCondition u v) :
-- imply
  DisjointWFscConvolutionCondition (𝓕 u) (𝓕 v) := by
-- proof
  apply WavefrontSet.disjointWFscProduct_implies_disjointWFscConvolution_fourier u v hcond


-- created on 2026-10-23
