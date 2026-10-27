import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagRecovery
open Finset StatMech StatMech.Ising


/--
[lpReplicaRowTag_eq_of_false_class_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitExactTagRecovery.lean)
-/
@[path]
private lemma lpReplicaRowTag_eq_of_false_class_iff_eq
  [Fintype V]
  [DecidableEq V]
  {a b : LPReplicaRowTag}
-- given
  (hrow : (a.1 = false ↔ b.1 = false))
  (hfalse : (a = (false, false) ↔ b = (false, false)))
  (htrue : (a = (true, false) ↔ b = (true, false))) :
-- imply
  a = b := by
-- proof
  apply StatMech.Ising.lpReplicaRowTag_eq_of_false_class_iff a b hrow hfalse htrue

/--
[lpReplica_mem_cast_finset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitExactTagRecovery.lean)
-/
@[path]
private lemma lpReplica_mem_cast_finset_eq
  [Fintype V]
  [DecidableEq V]
  [∀ j, DecidableEq (F j)]
  {a b : J}
  {x : F a}
  {S : Finset (F a)}
-- given
  (F : J -> Type*)
  (h : a = b) :
-- imply
  cast (congrArg F h) x ∈ cast (congrArg (fun j => Finset (F j)) h) S ↔ x ∈ S := by
-- proof
  apply StatMech.Ising.lpReplica_mem_cast_finset F h x S

/--
[lpReplicaOrbitCollisionSplitTag_of_tag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitExactTagRecovery.lean)
-/
@[path]
private lemma lpReplicaOrbitCollisionSplitTag_of_tag_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  let a := lpReplicaTaggedOriginProfile G sites m tag false let P := lpReplicaRowCopies G sites m tag false let Sa := lpReplicaTaggedRowCurrentSubset G sites m tag false false let Sb0 := lpReplicaReflectCopies G sites (lpReplicaTaggedRowProfile G sites m tag true) (lpReplicaTaggedRowCurrentSubset G sites m tag true false) let hb := lpReplicaTaggedOrigin_right_eq_reflectedResidual G sites m tag let Sb : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) (lpReplicaReflectedResidual G sites m a)) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitCollisionSplitTag_of_tag G sites m tag


-- created on 2026-10-23
