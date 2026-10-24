import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagProjection
open Finset StatMech StatMech.Ising


/--
[lpReplicaDecoratedOrbitAtomOfRowGate_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitExactTagProjection.lean)
-/
@[path]
private lemma lpReplicaDecoratedOrbitAtomOfRowGate_origin_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
  {L : LPReplicaProfileOrbitLabel G sites q m}
-- given
  (sites : I -> V)
  (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (hgate : LPReplicaRowGate G sites m A B tag) :
-- imply
  (lpReplicaDecoratedOrbitAtomOfRowGate G sites m q tag A B hm hgate L).1.2.1.1 = lpReplicaTaggedOriginProfile G sites m tag false := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedOrbitAtomOfRowGate_origin G sites m q tag A B hm hgate L

/--
[lpReplicaDecoratedOrbitAtomOfRowGate_currentRow0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitExactTagProjection.lean)
-/
@[path]
private lemma lpReplicaDecoratedOrbitAtomOfRowGate_currentRow0_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
  {L : LPReplicaProfileOrbitLabel G sites q m}
-- given
  (sites : I -> V)
  (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (hgate : LPReplicaRowGate G sites m A B tag) :
-- imply
  (lpReplicaDecoratedOrbitAtomOfRowGate G sites m q tag A B hm hgate L).1.2.2.1.1 = lpReplicaTaggedRowCurrentSubset G sites m tag false false := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedOrbitAtomOfRowGate_currentRow0 G sites m q tag A B hm hgate L

/--
[lpReplicaDecoratedOrbitAtomOfRowGate_currentRow1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitExactTagProjection.lean)
-/
@[path]
private lemma lpReplicaDecoratedOrbitAtomOfRowGate_currentRow1_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
  {L : LPReplicaProfileOrbitLabel G sites q m}
-- given
  (sites : I -> V)
  (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (hgate : LPReplicaRowGate G sites m A B tag) :
-- imply
  let Sb0 := lpReplicaReflectCopies G sites (lpReplicaTaggedRowProfile G sites m tag true) (lpReplicaTaggedRowCurrentSubset G sites m tag true false) let hb := lpReplicaTaggedOrigin_right_eq_reflectedResidual G sites m tag (lpReplicaDecoratedOrbitAtomOfRowGate G sites m q tag A B hm hgate L).1.2.2.2.1 = cast (congrArg (fun p => Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) p)) hb) Sb0 := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedOrbitAtomOfRowGate_currentRow1 G sites m q tag A B hm hgate L

/--
[lpReplicaOrientedFourColorTag_ofRowGate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitExactTagProjection.lean)
-/
@[path]
private lemma lpReplicaOrientedFourColorTag_ofRowGate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
  {L : LPReplicaProfileOrbitLabel G sites q m}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (hgate : LPReplicaRowGate G sites m A B tag) :
-- imply
  lpReplicaOrientedFourColorTag G sites A (B.map lpReplicaCurrentReflect.toEmbedding) q (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A (B.map lpReplicaCurrentReflect.toEmbedding) q (lpReplicaDecoratedOrbitAtomOfRowGate G sites m q tag A B hm hgate L)) = tag := by
-- proof
  apply StatMech.Ising.lpReplicaOrientedFourColorTag_ofRowGate G sites A B q m tag hm hgate L

/--
[lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitExactTagProjection.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  let B := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 lpReplicaOrientedFourColorTag G sites ∅ B q (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅ B q z) = (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData G sites i j q z


-- created on 2026-10-23
