import Mathlib
import Initialize.Tactic.Attr.Basic
import Class.Mathlib_IsModuleTopology


@[path]
private lemma main
  [CommRing R] [TopologicalSpace R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra R S] :
-- imply
  IsTopologicalModule R S ↔ Continuous (algebraMap R S) := by
-- proof
  refine ⟨fun _ ↦ continuous_algebraMap R S, fun h ↦ ?_⟩
  have : Continuous (fun rs ↦ algebraMap R S rs.1 • rs.2 : R × S → S) := by
    fun_prop
  simp_rw [← algebra_compatible_smul S] at this
  have : ContinuousSMul R S := ⟨this⟩
  apply IsTopologicalModule.mk


-- created on 2026-11-13
