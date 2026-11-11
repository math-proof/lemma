import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasurableSpace


/--
[measurability_from_generators](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MeasurabilityGenerators.lean)
-/
@[path]
lemma measurability_from_generators
  [MeasurableSpace α]
  {S : Set (Set β)}
  {f : α → β} :
-- imply
  @Measurable α β _ (generateFrom S) f ↔ ∀ s ∈ S, MeasurableSet (f ⁻¹' s) := by
-- proof
  constructor
  · intro hf s hs
    exact hf (measurableSet_generateFrom hs)
  · exact measurable_generateFrom


-- created on 2026-10-23
