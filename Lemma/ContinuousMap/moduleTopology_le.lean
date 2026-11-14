import Mathlib
import Initialize.Tactic.Attr.Basic
import Class.Mathlib_IsModuleTopology
open ModuleTopology


@[path]
private lemma main
  [CommRing R]
  [TopologicalSpace R]
  [CommRing S]
  [TopologicalSpace S]
  [Algebra R S]
  [AddCommGroup M]
  [Module R M]
  [Module S M]
  [IsScalarTower R S M]
  [IsTopologicalModule R S] :
-- imply
  moduleTopology R M ≤ moduleTopology S M := by
-- proof
  let instTS : TopologicalSpace M := moduleTopology S M
  have : ContinuousAdd M := continuousAdd S M
  have ⟨cts_smul⟩ : ContinuousSMul S M := continuousSMul S M
  suffices ContinuousSMul R M from _root_.moduleTopology_le R M
  constructor
  suffices Continuous (fun rm ↦ algebraMap R S rm.1 • rm.2 : R × M → M) by
    simpa [← algebra_compatible_smul S]
  fun_prop


-- created on 2026-11-13
