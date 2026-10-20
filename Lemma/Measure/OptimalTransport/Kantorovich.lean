import Mathlib
import sympy.Basic
import sympy.atlas.MeasureTheory.OptimalTransport.Kantorovich
open MeasureTheory
open scoped BoundedContinuousFunction CompactlySupported ENNReal
open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted


/--
[kantorovich_duality_compact](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean)
-/
@[path]
private lemma kantorovich_duality_compact_eq
  [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y] [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  {μ : ProbabilityMeasure X}
  {ν : ProbabilityMeasure Y}
  {c : X × Y → ℝ}
-- given
  (hc : Continuous c) :
-- imply
  sInf (primalValues μ ν c) =
    sSup {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
    DualFeasible c φ ψ ∧
    r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)} := by
-- proof
  apply MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted.kantorovich_duality_compact μ ν c hc


-- created on 2026-10-20
