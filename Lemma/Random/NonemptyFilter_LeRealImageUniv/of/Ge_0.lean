import sympy.stats.value_at_risk
import sympy.Basic
import Lemma.Random.RealLt_Inf'.eq.Zero
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {α : ℝ}
-- given
  (h₀ : 0 ≤ α)
  (X : Ω → ℝ) :
-- imply
  ((Finset.univ.image X).filter fun t => μ.real {ω | X ω < t} ≤ α).Nonempty := by
-- proof
  have := nonempty_of_isProbabilityMeasure μ
  obtain ⟨ω₀, -, h⟩ := Finset.univ.exists_mem_eq_inf' Finset.univ_nonempty X
  refine ⟨X ω₀, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem X (Finset.mem_univ ω₀), ?_⟩⟩
  rw [← h, Random.RealLt_Inf'.eq.Zero (μ := μ) X]
  exact h₀


-- created on 2026-09-26
