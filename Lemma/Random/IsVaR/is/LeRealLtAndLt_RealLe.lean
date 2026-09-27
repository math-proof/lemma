import sympy.stats.value_at_risk
import sympy.Basic
import Lemma.Random.IsQuantileLower.is.LeRealLt
import Lemma.Random.Any_LtAndEqSetOfLeSetOfLt
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ}
  {α v : ℝ} :
-- imply
  IsVaR μ X α v ↔ μ.real {ω | X ω < v} ≤ α ∧ α < μ.real {ω | X ω ≤ v} := by
-- proof
  constructor
  · intro h
    refine ⟨Random.IsQuantileLower.is.LeRealLt.mp h.isGreatest.1, not_le.mp fun hc => ?_⟩
    obtain ⟨q, hq, e⟩ := Random.Any_LtAndEqSetOfLeSetOfLt X v
    exact (h.isGreatest.2 (Random.IsQuantileLower.is.LeRealLt.mpr (e ▸ hc))).not_gt hq
  · intro h
    refine ⟨⟨Random.IsQuantileLower.is.LeRealLt.mpr h.1, fun q hq => not_lt.mp fun hc => ?_⟩⟩
    exact (h.2.trans_le ((measureReal_mono fun ω hω => lt_of_le_of_lt hω hc).trans (Random.IsQuantileLower.is.LeRealLt.mp hq))).false


-- created on 2026-09-26
