import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.TheoryOfProbability.code.MeasuresOnR
open Set Filter MeasureTheory ENNReal Topology (ofReal)
open ENNReal (ofReal)


/--
[stieltjes_measure_construction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MeasuresOnR.lean)
-/
@[path]
lemma stieltjes_measure_construction
  {f : StieltjesFunction ℝ}
-- given
  (hf_bot : Tendsto f atBot (𝓝 0))
  (hf_top : Tendsto f atTop (𝓝 1)) :
-- imply
  IsProbabilityMeasure f.measure ∧ (∀ a b : ℝ, a ≤ b → f.measure (Ioc a b) = ofReal (f b - f a)) ∧ (∀ ν : Measure ℝ, [IsFiniteMeasure ν] → (∀ a b : ℝ, a ≤ b → ν (Ioc a b) = ofReal (f b - f a)) → ν = f.measure) := by
-- proof
  refine ⟨f.isProbabilityMeasure hf_bot hf_top, fun a b _ => f.measure_Ioc a b, ?_⟩
  intro ν hν_inst hν
  haveI := hν_inst
  exact Measure.ext_of_Ioc ν f.measure (fun {a b} hab => by rw [hν a b hab.le, f.measure_Ioc])


-- created on 2026-10-23
