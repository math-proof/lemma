/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Atomless.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.MonotoneConvergence
import Def.MeasureTheory.Measure.Atomless


section

open MeasureTheory Set Filter Topology

namespace MeasureTheory

/-- The Sierpinski capacity is bounded by the target. -/
theorem sierpinskiCap_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} {t : ENNReal} {u : Set α} :
    sierpinskiCap μ s t u ≤ t := by
  change sSup _ ≤ t
  apply sSup_le
  rintro m ⟨v, _, _, hle, rfl⟩
  exact le_add_self.trans hle

/-- Choice of a greedy piece attaining at least half the Sierpinski capacity. -/
theorem sierpinskiChoice {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {s : Set α}
    {t : ENNReal} (ht : t ≤ μ s) {u : Set α} (hle : μ u ≤ t) :
    ∃ v, MeasurableSet v ∧ v ⊆ s \ u ∧ μ u + μ v ≤ t ∧
      sierpinskiCap μ s t u / 2 ≤ μ v := by
  by_cases hcap : sierpinskiCap μ s t u = 0
  · refine ⟨∅, MeasurableSet.empty, Set.empty_subset _, ?_, ?_⟩
    · simpa using hle
    · simp [hcap]
  · have hpos : 0 < sierpinskiCap μ s t u := bot_lt_iff_ne_bot.mpr hcap
    have ht_ne : t ≠ ⊤ := ne_top_of_le_ne_top (measure_lt_top μ s).ne ht
    have hcap_ne : sierpinskiCap μ s t u ≠ ⊤ :=
      ne_top_of_le_ne_top ht_ne sierpinskiCap_le
    have hhalf : sierpinskiCap μ s t u / 2 < sierpinskiCap μ s t u :=
      ENNReal.half_lt_self (ne_of_gt hpos) hcap_ne
    by_contra hcon
    have hall : ∀ v, MeasurableSet v → v ⊆ s \ u → μ u + μ v ≤ t →
        μ v ≤ sierpinskiCap μ s t u / 2 := by
      intro v hvmeas hvsub hle'
      by_contra hlt
      push Not at hlt
      exact hcon ⟨v, hvmeas, hvsub, hle', le_of_lt hlt⟩
    have hle2 : sierpinskiCap μ s t u ≤ sierpinskiCap μ s t u / 2 := by
      change sSup _ ≤ _
      apply sSup_le
      rintro m ⟨v, hvmeas, hvsub, hle', rfl⟩
      exact hall v hvmeas hvsub hle'
    exact (lt_irrefl _ (lt_of_le_of_lt hle2 hhalf)).elim

end MeasureTheory
end
