import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasurableSpace Set


/--
[pi_lambda_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PiLambdaSystem.lean)
-/
@[path]
lemma pi_lambda_theorem
  {S : Set (Set α)}
  {d : DynkinSystem α}
  {s : Set α}
-- given
  (hpi : IsPiSystem S)
  (hS : ∀ s ∈ S, d.Has s)
  (hs : @MeasurableSet α (generateFrom S) s) :
-- imply
  d.Has s := by
-- proof
  have h_gen_le : DynkinSystem.generate S ≤ d := d.generate_le hS
  rw [DynkinSystem.generateFrom_eq hpi] at hs
  exact h_gen_le s hs


-- created on 2026-10-23
