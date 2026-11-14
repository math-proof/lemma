import Mathlib
import Initialize.Tactic.Attr.Basic
import Class.Mathlib_IsModuleTopology
open ModuleTopology IsModuleTopology


@[path]
private lemma main
  [CommRing R]
  [TopologicalSpace R]
  [AddCommGroup M]
  [TopologicalSpace M]
  [Module R M]
  [IsModuleTopology R M] :
-- imply
  IsTopologicalModule R M := by
-- proof
  refine {
    continuous_smul := ?_
    continuous_add := ?_
  }
  · apply eq_moduleTopology R M ▸ (continuousSMul R M).1
  · apply eq_moduleTopology R M ▸ (continuousAdd R M).1


-- created on 2026-11-13
