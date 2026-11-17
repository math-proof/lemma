module

public import Mathlib
public import Theorem.Measure.IsFiniteMeasureOnCompacts_Comap.of.IsOpenEmbedding

public section

open Topology MeasureTheory Measure


/--
IsHaarMeasure is preserved under Measure.comap along an open embedding of topological groups.
-/
public theorem Measure.IsHaarMeasure_Comap.of.IsOpenEmbedding
  [Group G] [TopologicalSpace G] [MeasurableSpace G] [MeasurableMul G] [BorelSpace G]
  [Group H] [TopologicalSpace H] [MeasurableSpace H] [MeasurableMul H] [BorelSpace H]
  {φ : G →* H}
-- given
  (hφ : IsOpenEmbedding φ)
  (μ : Measure H)
  [IsHaarMeasure μ] :
-- imply
  IsHaarMeasure (comap φ μ) := by
-- proof
  refine
    { toIsMulLeftInvariant := IsMulLeftInvariant.comap μ hφ.measurableEmbedding
      toIsFiniteMeasureOnCompacts := IsFiniteMeasureOnCompacts_Comap.of.IsOpenEmbedding hφ μ
      toIsOpenPosMeasure := IsOpenPosMeasure.comap μ hφ }


-- created on 2026-10-24
