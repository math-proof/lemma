import Lemma.Random.KlDiv.eq.All_EqGetMap0.of.Measurable
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Initialize.Tactic.Attr.Basic
open Classical ENNReal InformationTheory MeasureTheory Random


private lemma witness [MeasurableSpace α] {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : ¬ ν ≪ μ) :
  ∃ φ : α → Bool, Measurable φ ∧ klDiv (ν.map φ) (μ.map φ) = ⊤ := by
  simp only [Measure.AbsolutelyContinuous, not_forall] at h
  obtain ⟨s, hμs, hνs⟩ := h
  obtain ⟨t, hst, ht, hμt⟩ := exists_measurable_superset_of_null hμs
  have hνt : ν t ≠ 0 := fun h0 => hνs (measure_mono_null hst h0)
  let φ : α → Bool := t.piecewise (fun _ => true) (fun _ => false)
  have hφ : Measurable φ := Measurable.piecewise ht measurable_const measurable_const
  refine ⟨φ, hφ, ?_⟩
  rw [KlDiv.eq.All_EqGetMap0.of.Measurable hφ]
  refine ite_eq_right ?_
  intro hall
  have hpre : φ ⁻¹' {true} = t := by
    ext x
    simp [φ, Set.piecewise, Set.mem_preimage]
  exact hνt <| by
    simpa [Measure.map_apply hφ (measurableSet_singleton _), hpre] using
      hall true (by simpa [Measure.map_apply hφ (measurableSet_singleton _), hpre] using hμt)

/--
If one probability fails to be absolutely continuous with respect to another, a two-point measurable
map already sends their Kullback–Leibler divergence to `⊤`. The supremum of the partition
divergences is therefore infinite whenever the divergence itself is infinite for lack of absolute
continuity.
-/
@[path]
private lemma main
  [MeasurableSpace α]
  {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
-- given
  (h : ¬ ν ≪ μ) :
-- imply
  ∃ φ : α → Bool, Measurable φ ∧ klDiv (ν.map φ) (μ.map φ) = ⊤ :=
-- proof
  witness h


-- created on 2026-11-02
