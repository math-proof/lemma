import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.Part4
open StatMech StatMech.Ising


/--
[lpReplicaCurrentFoldedEdge_isDiag_of_mem_orbitFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean)
-/
@[path]
private lemma lpReplicaCurrentFoldedEdge_isDiag_of_mem_orbitFixed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {e : (lpReplicaCurrentGraph G sites).edgeFinset}
-- given
  (sites : I -> V)
  (hfixed : e ∈ lpReplicaCurrentEdgeOrbitFixed G sites) :
-- imply
  (lpReplicaCurrentFoldedEdge G sites e).IsDiag := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentFoldedEdge_isDiag_of_mem_orbitFixed G sites e hfixed

/--
[lpReplicaProfileCopyEquivCommonSlot_eq_inr_of_folded_not_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean)
-/
@[path]
private lemma lpReplicaProfileCopyEquivCommonSlot_eq_inr_of_folded_not_diag_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {d : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (hdiag : ¬ (lpReplicaCurrentFoldedEdge G sites d.1).IsDiag) :
-- imply
  ∃ x, lpReplicaProfileCopyEquivCommonSlot G sites q m hm L d = Sum.inr x := by
-- proof
  apply StatMech.Ising.lpReplicaProfileCopyEquivCommonSlot_eq_inr_of_folded_not_diag G sites q m hm L d hdiag

/--
[lpReplicaOrbitFourColorSlotReflectRowToggle_strictSingleton_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotReflectRowToggle_strictSingleton_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {s : LPReplicaOrbitFourColorSlotState G sites q}
  {row : Finset (LPReplicaOrbitCommonSlot G sites q)}
  {d e : LPReplicaOrbitCommonSlot G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hd : ∃ x, d = Sum.inr x)
  (he : ∃ x, e = Sum.inr x)
  (hstate : lpReplicaOrbitFourColorSlotReflectRowToggle G sites q {d} row s = lpReplicaOrbitFourColorSlotReflectRowToggle G sites q {e} row s) :
-- imply
  d = e := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotReflectRowToggle_strictSingleton_injective G sites q s row hd he hstate

/--
[lpReplicaOrbitCommonSlotsOfCopies_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean)
-/
@[path]
private lemma lpReplicaOrbitCommonSlotsOfCopies_singleton_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {c : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L {c} = {lpReplicaProfileCopyEquivCommonSlot G sites q m hm L c} := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitCommonSlotsOfCopies_singleton G sites q m hm L c

/--
[lpReplicaAggregateDecoratedSource_indices_eq_of_pairCode_orientation_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedSource_indices_eq_of_pairCode_orientation_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z w : LPReplicaAggregateDecoratedSource G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hpair : s(z.1, z.2.1) = s(w.1, w.2.1))
  (horientation : (lpReplicaAggregateDecoratedSourcePairCode G sites q z).1 = (lpReplicaAggregateDecoratedSourcePairCode G sites q w).1) :
-- imply
  z.1 = w.1 ∧ z.2.1 = w.2.1 := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedSource_indices_eq_of_pairCode_orientation_eq G sites q z w hpair horientation

/--
[lpReplicaStrictRoute_markedPair_eq_of_third_eq_of_routePair_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean)
-/
@[path]
private lemma lpReplicaStrictRoute_markedPair_eq_of_third_eq_of_routePair_eq_eq
  [Fintype V]
  [DecidableEq V]
  {i j k u v i' j' u' v' : I}
-- given
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hjk : j ≠ k)
  (hij' : i' ≠ j')
  (hik' : i' ≠ k)
  (hjk' : j' ≠ k)
  (hu : u = i ∨ u = j ∨ u = k)
  (hv : v = i ∨ v = j ∨ v = k)
  (huv : u ≠ v)
  (hu' : u' = i' ∨ u' = j' ∨ u' = k)
  (hv' : v' = i' ∨ v' = j' ∨ v' = k)
  (huv' : u' ≠ v')
  (hthird : lpReplicaThirdOfThree i j k u v = lpReplicaThirdOfThree i' j' k u' v')
  (hroute : s(u, v) = s(u', v')) :
-- imply
  s(i, j) = s(i', j') := by
-- proof
  apply StatMech.Ising.lpReplicaStrictRoute_markedPair_eq_of_third_eq_of_routePair_eq hij hik hjk hij' hik' hjk' hu hv huv hu' hv' huv' hthird hroute

/--
[lpReplica_sitePair_eq_of_currentPhysicalPair_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean)
-/
@[path]
private lemma lpReplica_sitePair_eq_of_currentPhysicalPair_eq_eq
  [Fintype V]
  [DecidableEq V]
  {u v u' v' : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hpair : s((Sum.inl (sites u) : V ⊕ Unit), Sum.inl (sites v)) = s((Sum.inl (sites u') : V ⊕ Unit), Sum.inl (sites v'))) :
-- imply
  s(u, v) = s(u', v') := by
-- proof
  apply StatMech.Ising.lpReplica_sitePair_eq_of_currentPhysicalPair_eq sites hsite hpair

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_orientation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_orientation_eq
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
  (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget G sites hsite q hcard z d).1 = (lpReplicaAggregateDecoratedSourcePairCode G sites q (z.toAggregate G sites q)).1 := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_orientation G sites hsite q hcard z d

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_selectedSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_selectedSeam_eq
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
  (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget G sites hsite q hcard z d).2.1 = lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q (z.toAggregate G sites q) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_selectedSeam G sites hsite q hcard z d

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_thirdSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_thirdSeam_eq
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
  let a := z.toAggregate G sites q let k := lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q a let route := lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate G sites hsite q hcard z d (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget G sites hsite q hcard z d).2.2.1 = lpReplicaThirdOfThree a.1 a.2.1 k route.u route.v := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_thirdSeam G sites hsite q hcard z d

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot_folded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot_folded_eq
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
  let route := lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate G sites hsite q hcard z d lpReplicaOrbitFoldedSlotEnds G sites q (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot G sites hsite q z d) = s(Sum.inl (sites route.u), Sum.inl (sites route.v)) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot_folded G sites hsite q hcard z d

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState_eq
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
  let a := z.toAggregate G sites q let route := lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate G sites hsite q hcard z d lpReplicaAggregateDecoratedTargetSlotState G sites q (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget G sites hsite q hcard z d) = lpReplicaOrbitFourColorSlotReflectRowToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q a.2.2.2.1.1.1 a.2.2.2.1.1.2 a.2.2.2.2.2 {route.d}) (lpReplicaOrbitCommonSlotsOfCopies G sites q a.2.2.2.1.1.1 a.2.2.2.1.1.2 a.2.2.2.2.2 {route.c}) (lpReplicaOffdiagDecoratedSourceSlotState G sites a.1 a.2.1 q a.2.2.2) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState G sites hsite q hcard z d

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState_singletons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState_singletons_eq
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
  let a := z.toAggregate G sites q lpReplicaAggregateDecoratedTargetSlotState G sites q (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget G sites hsite q hcard z d) = lpReplicaOrbitFourColorSlotReflectRowToggle G sites q {lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot G sites hsite q z d} {lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateRowSlot G sites hsite q z} (lpReplicaOffdiagDecoratedSourceSlotState G sites a.1 a.2.1 q a.2.2.2) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState_singletons G sites hsite q hcard z d

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFive_rowMask_eq_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFive_rowMask_eq_univ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  let a := z.toAggregate G sites q lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedSourceSlotState G sites a.1 a.2.1 q a.2.2.2) = Finset.univ := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFive_rowMask_eq_univ G sites hsite q hcard z

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateIndices_eq_of_spatialSlot_eq_of_target_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateIndices_eq_of_spatialSlot_eq_of_target_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z w : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
  {d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z)}
  {e : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q w)}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hspatial : lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot G sites hsite q z d = lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot G sites hsite q w e)
  (htarget : lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget G sites hsite q hcard z d = lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget G sites hsite q hcard w e) :
-- imply
  let a := z.toAggregate G sites q let b := w.toAggregate G sites q a.1 = b.1 ∧ a.2.1 = b.2.1 := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateIndices_eq_of_spatialSlot_eq_of_target_eq G sites hsite q hcard z w d e hspatial htarget

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSource_eq_of_indices_eq_of_spatialSlot_eq_of_target_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSource_eq_of_indices_eq_of_spatialSlot_eq_of_target_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z w : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
  {d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z)}
  {e : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q w)}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hindices : (z.toAggregate G sites q).1 = (w.toAggregate G sites q).1 ∧ (z.toAggregate G sites q).2.1 = (w.toAggregate G sites q).2.1)
  (hspatial : lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot G sites hsite q z d = lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot G sites hsite q w e)
  (htarget : lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget G sites hsite q hcard z d = lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget G sites hsite q hcard w e) :
-- imply
  z = w := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSource_eq_of_indices_eq_of_spatialSlot_eq_of_target_eq G sites hsite q hcard z w d e hindices hspatial htarget

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSource_eq_of_spatialSlot_eq_of_target_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSource_eq_of_spatialSlot_eq_of_target_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z w : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
  {d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z)}
  {e : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q w)}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hspatial : lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot G sites hsite q z d = lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot G sites hsite q w e)
  (htarget : lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget G sites hsite q hcard z d = lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget G sites hsite q hcard w e) :
-- imply
  z = w := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSource_eq_of_spatialSlot_eq_of_target_eq G sites hsite q hcard z w d e hspatial htarget

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  Function.Injective (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget G sites hsite q hcard z) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_injective G sites hsite q hcard z

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_hasDoubleIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_hasDoubleIncidence_eq
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
  LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites q (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget G sites hsite q hcard z d) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_hasDoubleIncidence G sites hsite q hcard z d


-- created on 2026-10-23
