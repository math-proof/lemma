import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.IsModuleTopology
open IsModuleTopology


@[path]
private lemma main
  [CommRing R]
  [TopologicalSpace R]
  [IsTopologicalRing R]
  [Ring D]
  [Algebra R D]
  [Module.Finite R D]
  [TopologicalSpace D]
  [IsModuleTopology R D] :
-- imply
  IsTopologicalSemiring D := by
-- proof
  refine {
    continuous_add := ?_
    continuous_mul := ?_
  }
  · apply (toContinuousAdd R D).1
  · apply continuous_mul' R D


-- created on 2026-11-13
