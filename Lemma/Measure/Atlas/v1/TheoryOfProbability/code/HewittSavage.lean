import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TheoryOfProbability.code.HewittSavage
open MeasureTheory MeasurableSpace ProbabilityTheory Filter Set
open scoped ENNReal MeasureTheory


/--
[IsExchangeableEventWrt.measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/HewittSavage.lean)
-/
@[path]
lemma IsExchangeableEventWrt.measurableSet
  [MeasurableSpace Ω]
  [MeasurableSpace S]
  {X : ℕ → Ω → S}
  {E : Set Ω}
-- given
  (hX : ∀ n, Measurable (X n))
  (hE : IsExchangeableEventWrt X E) :
-- imply
  MeasurableSet E := by
-- proof
  obtain ⟨A, ⟨hA_meas, _⟩, rfl⟩ := hE
  exact (measurable_pi_lambda _ (fun n => hX n)) hA_meas
/-- **Hewitt–Savage 0–1 law**. If `X_1, X_2, …` is an i.i.d. sequence (independent
and identically distributed) and `E` is an exchangeable event (i.e. `E ∈ ℰ`, the
σ-field of permutable events) with respect to `X`, then `μ E ∈ {0, 1}`. -/


-- created on 2026-10-23
