import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitTagReconstruction
open Finset StatMech StatMech.Ising


/--
[lpReplicaRowCopies_true_eq_compl_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitTagReconstruction.lean)
-/
@[path]
private lemma lpReplicaRowCopies_true_eq_compl_false_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaRowCopies G sites m tag true = Finset.univ \ lpReplicaRowCopies G sites m tag false := by
-- proof
  apply StatMech.Ising.lpReplicaRowCopies_true_eq_compl_false G sites m tag

/--
[lpReplicaTaggedOrigin_collisionProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitTagReconstruction.lean)
-/
@[path]
private lemma lpReplicaTaggedOrigin_collisionProfile_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaCollisionProfile G sites (lpReplicaTaggedOriginProfile G sites m tag false) (lpReplicaTaggedOriginProfile G sites m tag true) = m := by
-- proof
  apply StatMech.Ising.lpReplicaTaggedOrigin_collisionProfile G sites m tag

/--
[lpReplicaTaggedOrigin_left_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitTagReconstruction.lean)
-/
@[path]
private lemma lpReplicaTaggedOrigin_left_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaTaggedOriginProfile G sites m tag false <= m := by
-- proof
  apply StatMech.Ising.lpReplicaTaggedOrigin_left_le G sites m tag

/--
[lpReplicaTaggedRowBackEmbedding_ends](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitTagReconstruction.lean)
-/
@[path]
private lemma lpReplicaTaggedRowBackEmbedding_ends_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {row : Bool}
  {c : Copy (lpReplicaCurrentGraph G sites) (lpReplicaTaggedRowProfile G sites m tag row)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  endsM (lpReplicaCurrentGraph G sites) m (lpReplicaTaggedRowBackEmbedding G sites m tag row c) = endsM (lpReplicaCurrentGraph G sites) (lpReplicaTaggedRowProfile G sites m tag row) c := by
-- proof
  apply StatMech.Ising.lpReplicaTaggedRowBackEmbedding_ends G sites m tag row c

/--
[lpReplicaTaggedRowCurrentSubset_map_back](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitTagReconstruction.lean)
-/
@[path]
private lemma lpReplicaTaggedRowCurrentSubset_map_back_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {row current : Bool}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  (lpReplicaTaggedRowCurrentSubset G sites m tag row current).map (lpReplicaTaggedRowBackEmbedding G sites m tag row) = lpReplicaCurrentCopies G sites m tag row current := by
-- proof
  apply StatMech.Ising.lpReplicaTaggedRowCurrentSubset_map_back G sites m tag row current

/--
[lpReplicaTaggedRowCurrentSubset_true_eq_compl_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitTagReconstruction.lean)
-/
@[path]
private lemma lpReplicaTaggedRowCurrentSubset_true_eq_compl_false_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {row : Bool}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaTaggedRowCurrentSubset G sites m tag row true = Finset.univ \ lpReplicaTaggedRowCurrentSubset G sites m tag row false := by
-- proof
  apply StatMech.Ising.lpReplicaTaggedRowCurrentSubset_true_eq_compl_false G sites m tag row

/--
[lpReplicaTaggedRowCurrentSubset_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitTagReconstruction.lean)
-/
@[path]
private lemma lpReplicaTaggedRowCurrentSubset_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {row current : Bool}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  StatMech.Sharpness.RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) (lpReplicaTaggedRowProfile G sites m tag row)) (lpReplicaTaggedRowCurrentSubset G sites m tag row current) = StatMech.Sharpness.RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaCurrentCopies G sites m tag row current) := by
-- proof
  apply StatMech.Ising.lpReplicaTaggedRowCurrentSubset_sources G sites m tag row current

/--
[lpReplicaTaggedRow_univ_map_back](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitTagReconstruction.lean)
-/
@[path]
private lemma lpReplicaTaggedRow_univ_map_back_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {row : Bool}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) (lpReplicaTaggedRowProfile G sites m tag row))).map (lpReplicaTaggedRowBackEmbedding G sites m tag row) = lpReplicaRowCopies G sites m tag row := by
-- proof
  apply StatMech.Ising.lpReplicaTaggedRow_univ_map_back G sites m tag row

/--
[lpReplicaTaggedRow_ghost_disconn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitTagReconstruction.lean)
-/
@[path]
private lemma lpReplicaTaggedRow_ghost_disconn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {row : Bool}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hdisc : ¬ StatMech.Sharpness.RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaRowCopies G sites m tag row) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
-- imply
  ¬ StatMech.Sharpness.RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) (lpReplicaTaggedRowProfile G sites m tag row)) Finset.univ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplicaTaggedRow_ghost_disconn G sites m tag row hdisc

/--
[lpReplicaTaggedRowCurrentSubset_mem_disconnFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitTagReconstruction.lean)
-/
@[path]
private lemma lpReplicaTaggedRowCurrentSubset_mem_disconnFamily_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
  {row : Bool}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m A B tag) :
-- imply
  lpReplicaTaggedRowCurrentSubset G sites m tag row false ∈ lpReplicaDisconnProfileFamily G sites (if row then B else A) (lpReplicaTaggedRowProfile G sites m tag row) := by
-- proof
  apply StatMech.Ising.lpReplicaTaggedRowCurrentSubset_mem_disconnFamily G sites m tag A B hgate row

/--
[lpReplicaDisconnProfileFamily_reflect_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitTagReconstruction.lean)
-/
@[path]
private lemma lpReplicaDisconnProfileFamily_reflect_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A : Finset (LPReplicaCurrentVertex V)}
  {S : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hS : S ∈ lpReplicaDisconnProfileFamily G sites A m) :
-- imply
  lpReplicaReflectCopies G sites m S ∈ lpReplicaDisconnProfileFamily G sites (A.map lpReplicaCurrentReflect.toEmbedding) (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) := by
-- proof
  apply StatMech.Ising.lpReplicaDisconnProfileFamily_reflect_mem G sites A m S hS

/--
[lpReplicaTaggedOrigin_right_eq_reflectedResidual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitTagReconstruction.lean)
-/
@[path]
private lemma lpReplicaTaggedOrigin_right_eq_reflectedResidual_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaTaggedOriginProfile G sites m tag true = lpReplicaReflectedResidual G sites m (lpReplicaTaggedOriginProfile G sites m tag false) := by
-- proof
  apply StatMech.Ising.lpReplicaTaggedOrigin_right_eq_reflectedResidual G sites m tag

/--
[lpReplicaTaggedRowOne_reflectedCurrentSubset_mem_disconnFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitTagReconstruction.lean)
-/
@[path]
private lemma lpReplicaTaggedRowOne_reflectedCurrentSubset_mem_disconnFamily_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m A B tag) :
-- imply
  lpReplicaReflectCopies G sites (lpReplicaTaggedRowProfile G sites m tag true) (lpReplicaTaggedRowCurrentSubset G sites m tag true false) ∈ lpReplicaDisconnProfileFamily G sites (B.map lpReplicaCurrentReflect.toEmbedding) (lpReplicaTaggedOriginProfile G sites m tag true) := by
-- proof
  apply StatMech.Ising.lpReplicaTaggedRowOne_reflectedCurrentSubset_mem_disconnFamily G sites m tag A B hgate

/--
[exists_lpReplicaOrbitConfiguration_of_rowGate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitTagReconstruction.lean)
-/
@[path]
private lemma exists_lpReplicaOrbitConfiguration_of_rowGate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (hgate : LPReplicaRowGate G sites m A B tag) :
-- imply
  ∃ x : LPReplicaOrbitConfiguration G sites A (B.map lpReplicaCurrentReflect.toEmbedding) q, x.1.1 = m := by
-- proof
  apply StatMech.Ising.exists_lpReplicaOrbitConfiguration_of_rowGate G sites m q tag A B hm hgate


-- created on 2026-10-23
