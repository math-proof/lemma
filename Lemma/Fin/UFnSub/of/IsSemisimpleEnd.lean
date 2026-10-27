import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.LieGroups.code.SL2Basics.Part4
import Lemma.Nat.basisHC.eq.SMul
open Polynomial


/--
[semisimple_sub_smul_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2FiniteDimReps.lean)
-/
@[path]
private lemma main
  [Field K]
  [AddCommGroup V]
  [Module K V]
  {f : V →ₗ[K] V}
  {c : K}
-- given
  (hf : Module.End.IsSemisimple f) :
-- imply
  Module.End.IsSemisimple (f - c • LinearMap.id) := by
-- proof
  rw [show c • (LinearMap.id : V →ₗ[K] V) = algebraMap K _ c from by
    simp [Algebra.algebraMap_eq_smul_one]; rfl]
  exact Module.End.isSemisimple_sub_algebraMap_iff.mpr hf


-- created on 2026-10-23
-- updated on 2026-10-26
