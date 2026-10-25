/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Order.Compact
import Theorem.MeasureTheory.OptimalTransport.Kantorovich.Part2


section

open MeasureTheory

open scoped BoundedContinuousFunction CompactlySupported ENNReal

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/-- A finite Borel measure on a compact metric space is regular. -/
instance regular_of_finite_compact_metric
    {W : Type*} [MetricSpace W] [CompactSpace W]
    [MeasurableSpace W] [BorelSpace W]
    {μ : Measure W} [IsFiniteMeasure μ] : μ.Regular := by
  have hfin : IsFiniteMeasureOnCompacts μ := ⟨by
    intro K hK
    exact lt_of_le_of_lt (measure_mono (Set.subset_univ _)) (measure_lt_top μ _)⟩
  have hinner_open : μ.InnerRegularWRT IsCompact IsOpen :=
    innerRegularWRT_isCompact_isOpen μ
  have hinner_meas : μ.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) MeasurableSet :=
    innerRegular_isCompact_isClosed_measurableSet_of_finite μ
  have houter : μ.OuterRegular := ⟨fun {A} hA r hr => by
    by_cases hrU : r ≤ μ Set.univ
    · have hAfin : μ A ≠ ∞ := measure_ne_top μ A
      have hUfin : μ Set.univ ≠ ∞ := measure_ne_top μ Set.univ
      have hrfin : r ≠ ∞ := ne_top_of_le_ne_top hUfin hrU
      have hcompl : μ Aᶜ = μ Set.univ - μ A := measure_compl hA hAfin
      have hr'lt : μ Set.univ - r < μ Aᶜ := by
        rw [hcompl]
        exact ennreal_sub_lt_of_lt hUfin hAfin hrfin hr hrU
      obtain ⟨K, hKA, ⟨hKcomp, hKclosed⟩, hr'K⟩ :=
        hinner_meas hA.compl (μ Set.univ - r) hr'lt
      have hKfin : μ K ≠ ∞ := measure_ne_top μ K
      have hKmeas : MeasurableSet K := hKclosed.measurableSet
      have hKU : μ K ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      refine ⟨Kᶜ, fun x hx => ?_, hKclosed.isOpen_compl, ?_⟩
      · simp only [Set.mem_compl_iff]
        exact fun hKx => hKA hKx hx
      · rw [measure_compl hKmeas hKfin]
        have h1 : (μ Set.univ - μ K).toReal < r.toReal := by
          rw [ENNReal.toReal_sub_of_le hKU hUfin]
          have hr'K' : (μ Set.univ - r).toReal < (μ K).toReal := by
            have hsub : μ Set.univ - r ≠ ∞ :=
              ne_top_of_le_ne_top hUfin tsub_le_self
            exact (ENNReal.toReal_lt_toReal hsub hKfin).mpr hr'K
          rw [ENNReal.toReal_sub_of_le hrU hUfin] at hr'K'
          linarith
        have h2 : μ Set.univ - μ K ≠ ∞ := ne_top_of_le_ne_top hUfin tsub_le_self
        exact (ENNReal.toReal_lt_toReal h2 hrfin).mp h1
    · exact ⟨Set.univ, Set.subset_univ _, isOpen_univ, lt_of_not_ge hrU⟩⟩
  exact Measure.Regular.mk (toIsFiniteMeasureOnCompacts := hfin)
    (toOuterRegular := houter) hinner_open

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted
end
