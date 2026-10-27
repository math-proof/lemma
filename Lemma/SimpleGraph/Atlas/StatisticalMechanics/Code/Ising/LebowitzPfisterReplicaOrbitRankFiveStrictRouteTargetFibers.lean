import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteTargetFibers.Part2
open StatMech StatMech.Ising


/--
[lpReplicaOrbitFourColorSlotEnds_reflectRowToggle_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteTargetFibers.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotEnds_reflectRowToggle_singleton_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {s : LPReplicaOrbitFourColorSlotState G sites q}
  {row : Finset (LPReplicaOrbitCommonSlot G sites q)}
  {d x : LPReplicaOrbitCommonSlot G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hd : exists e, d = Sum.inr e) :
-- imply
  lpReplicaOrbitFourColorSlotEnds G sites q (lpReplicaOrbitFourColorSlotReflectRowToggle G sites q {d} row s) x = if x = d then Sym2.map lpReplicaCurrentReflect (lpReplicaOrbitFourColorSlotEnds G sites q s x) else lpReplicaOrbitFourColorSlotEnds G sites q s x := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotEnds_reflectRowToggle_singleton G sites q s row d x hd

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_rowMask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteTargetFibers.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_rowMask_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
  {d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z)}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaAggregateDecoratedTargetSlotState G sites q (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget G sites hsite q hcard z d)) = Finset.univ \ {lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateRowSlot G sites hsite q z} := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_rowMask G sites hsite q hcard z d

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotEnds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteTargetFibers.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotEnds_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
  {d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z)}
  {x : LPReplicaOrbitCommonSlot G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  let a := z.toAggregate G sites q let sourceState := lpReplicaOffdiagDecoratedSourceSlotState G sites a.1 a.2.1 q a.2.2.2 let spatial := lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot G sites hsite q z d lpReplicaOrbitFourColorSlotEnds G sites q (lpReplicaAggregateDecoratedTargetSlotState G sites q (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget G sites hsite q hcard z d)) x = if x = spatial then Sym2.map lpReplicaCurrentReflect (lpReplicaOrbitFourColorSlotEnds G sites q sourceState x) else lpReplicaOrbitFourColorSlotEnds G sites q sourceState x := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotEnds G sites hsite q hcard z d x

/--
[lpReplicaOffdiagDecoratedSourceSlotEnds_copy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteTargetFibers.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSourceSlotEnds_copy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {c : Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaOrbitFourColorSlotEnds G sites q (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1 z.1.1.2 z.2.2 c) = endsM (lpReplicaCurrentGraph G sites) z.1.1.1 c := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSourceSlotEnds_copy G sites i j q z c

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_spatialWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteTargetFibers.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_spatialWitness_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
  {d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z)}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness G sites q (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget G sites hsite q hcard z d) (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot G sites hsite q z d) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_spatialWitness G sites hsite q hcard z d

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidate_of_spatialWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteTargetFibers.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidate_of_spatialWitness_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
  {d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z)}
  {x : LPReplicaOrbitCommonSlot G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hx : LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness G sites q (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget G sites hsite q hcard z d) x) :
-- imply
  ∃ e : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z), lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot G sites hsite q z e = x := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidate_of_spatialWitness G sites hsite q hcard z d x hx


-- created on 2026-10-23
