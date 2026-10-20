import Mathlib
import sympy.Basic
import sympy.atlas.MeasureTheory.Integral.LyapunovConvexity
open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace
open MathlibExt.MeasureTheory.Integral.LyapunovConvexityWanted


/--
[lyapunov_convexity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Integral/LyapunovConvexity.lean)
-/
@[path]
private lemma lyapunov_convexity_eq
  [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {μ : Measure α} [IsFiniteMeasure μ]
  {f : α → E}
-- given
  (hf : Integrable f μ)
  (hAtomless : IsAtomless μ) :
-- imply
  IsCompact (lyapunovRange (μ := by
-- proof
  apply MathlibExt.MeasureTheory.Integral.LyapunovConvexityWanted.lyapunov_convexity f hf hAtomless


-- created on 2026-10-20
