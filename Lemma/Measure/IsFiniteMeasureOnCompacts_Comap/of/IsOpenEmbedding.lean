import Mathlib
import Initialize.Tactic.Attr.Basic
open Topology MeasureTheory Measure


/--
IsFiniteMeasureOnCompacts is preserved under Measure.comap along an open embedding.
-/
@[path]
private lemma main
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {φ : X → Y}
-- given
  (hφ : IsOpenEmbedding φ)
  (μ : Measure Y)
  [IsFiniteMeasureOnCompacts μ] :
-- imply
  IsFiniteMeasureOnCompacts (comap φ μ) := by
-- proof
  refine ⟨fun K hK => ?_⟩
  rw [MeasurableEmbedding.comap_apply hφ.measurableEmbedding]
  apply IsFiniteMeasureOnCompacts.lt_top_of_isCompact
  apply hK.image
  apply hφ.continuous


-- created on 2026-10-24
