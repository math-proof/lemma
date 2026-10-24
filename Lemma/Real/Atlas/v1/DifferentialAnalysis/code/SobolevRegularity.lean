import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.SobolevRegularity
open MeasureTheory SobolevSpace TemperedDistributions SobolevRegularity
open scoped FourierTransform SchwartzMap


namespace SobolevRegularity

/--
[sobolev_iff_derivatives_in_L2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevRegularity.lean)
-/
@[path]
lemma sobolev_iff_derivatives_in_L2
  {n : ℕ}
  {m : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  MemHs n (m : ℝ) u ↔ AllDerivMemL2 n m u :=
-- proof
  sobolev_integer_iff_deriv_memL2 m u
end SobolevRegularity



-- created on 2026-10-23
