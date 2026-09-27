import sympy.stats.value_at_risk
import sympy.Basic
import Lemma.Random.NonemptyFilter_LeRealImageUniv.of.Ge_0
import Lemma.Random.Lt_Sup'.of.LtRealLe_1
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ}
  {α : ℝ}
-- given
  (h₀ : 0 ≤ α)
  (h₁ : α < 1) :
-- imply
  μ.real {ω | X ω < finVaR μ X α} ≤ α ∧ α < μ.real {ω | X ω ≤ finVaR μ X α} := by
-- proof
  have := nonempty_of_isProbabilityMeasure μ
  have hS := Random.NonemptyFilter_LeRealImageUniv.of.Ge_0 (μ := μ) h₀ X
  unfold finVaR
  rw [dif_pos hS]
  refine ⟨(Finset.mem_filter.mp (Finset.max'_mem _ hS)).2, not_le.mp fun hg => ?_⟩
  obtain ⟨ω₀, -, hω₀⟩ := Finset.univ.exists_mem_eq_sup' Finset.univ_nonempty X
  let T := (Finset.univ.image X).filter (Finset.max' _ hS < ·)
  have hT : T.Nonempty := ⟨X ω₀, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem X (Finset.mem_univ ω₀), hω₀ ▸ Random.Lt_Sup'.of.LtRealLe_1 (μ := μ) (lt_of_le_of_lt hg h₁)⟩⟩
  obtain ⟨hq, hq'⟩ := Finset.mem_filter.mp (T.min'_mem hT)
  apply (Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hq, ?_⟩)).not_gt hq'
  apply le_trans _ hg
  refine measureReal_mono ?_ (measure_ne_top μ _)
  intro ω hω
  exact not_lt.mp fun hc => (T.min'_le (X ω) (Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem X (Finset.mem_univ ω), hc⟩)).not_gt hω


-- created on 2026-09-26
