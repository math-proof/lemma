import Mathlib
import Lemma.Definitions.Def_Mathlib_MeasureTheory_Group_Action
import Lemma.Definitions.Def_Mathlib_MeasureTheory_Measure_Typeclasses_Finite

section

open Topology MeasureTheory Measure

@[to_additive]
lemma Topology.IsOpenEmbedding.isHaarMeasure_comap {G H : Type*}
    [Group G] [TopologicalSpace G] [MeasurableSpace G] [MeasurableMul G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [MeasurableSpace H] [MeasurableMul H] [BorelSpace H]
    {φ : G →* H} (hφ : IsOpenEmbedding φ) (μ : Measure H) [IsHaarMeasure μ] :
    IsHaarMeasure (comap φ μ) where
  map_mul_left_eq_self := (hφ.measurableEmbedding.isMulLeftInvariant_comap μ).map_mul_left_eq_self
  lt_top_of_isCompact := (hφ.isFiniteMeasureOnCompacts_comap μ).lt_top_of_isCompact
  open_pos := (IsOpenPosMeasure.comap μ hφ).open_pos
