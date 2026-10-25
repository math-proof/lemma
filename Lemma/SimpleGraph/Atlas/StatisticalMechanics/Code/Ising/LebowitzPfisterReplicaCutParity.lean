import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCutParity.Part2
open Finset SimpleGraph StatMech StatMech.Ising StatMech.Ising.ReplicaCutParity


/--
[sources_inter_even_of_no_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCutParity.lean)
-/
@[path]
private lemma sources_inter_even_of_no_cross_eq
  [Fintype W]
  [DecidableEq W]
  {K : Finset ι}
  {S : Finset W}
-- given
  (ends : ι -> Sym2 W)
  (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag)
  (hno : ∀ {u v}, u ∈ S -> v ∉ S -> ¬ RandomCurrent.connK ends K u v) :
-- imply
  Even (#(RandomCurrent.sources ends K ∩ S)) := by
-- proof
  apply StatMech.Ising.ReplicaCutParity.sources_inter_even_of_no_cross ends K hnd S hno

/--
[exists_cross_connection_of_odd_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCutParity.lean)
-/
@[path]
private lemma exists_cross_connection_of_odd_sources_eq
  [Fintype W]
  [DecidableEq W]
  {K : Finset ι}
  {S : Finset W}
-- given
  (ends : ι -> Sym2 W)
  (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag)
  (hodd : Odd (#(RandomCurrent.sources ends K ∩ S))) :
-- imply
  ∃ u ∈ S, ∃ v ∉ S, RandomCurrent.connK ends K u v := by
-- proof
  apply StatMech.Ising.ReplicaCutParity.exists_cross_connection_of_odd_sources ends K hnd S hodd

/--
[lpReplicaCurrent_exists_crossConnection_of_odd_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCutParity.lean)
-/
@[path]
private lemma lpReplicaCurrent_exists_crossConnection_of_odd_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hodd : Odd (#(StatMech.Sharpness.sources (lpReplicaCurrentGraph G sites) (ofEdgeFun (lpReplicaCurrentGraph G sites) m) ∩ lpReplicaCurrentLeftSide))) :
-- imply
  ∃ u ∈ lpReplicaCurrentLeftSide, ∃ v ∉ lpReplicaCurrentLeftSide, CurrentConnected (lpReplicaCurrentGraph G sites) (ofEdgeFun (lpReplicaCurrentGraph G sites) m) u v := by
-- proof
  apply StatMech.Ising.lpReplicaCurrent_exists_crossConnection_of_odd_sources G sites m hodd

/--
[lpReplicaCurrent_exists_positiveSeam_of_crossConnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCutParity.lean)
-/
@[path]
private lemma lpReplicaCurrent_exists_positiveSeam_of_crossConnection_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {n : Current (LPReplicaCurrentVertex V)}
  {u v : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (hu : u ∈ lpReplicaCurrentLeftSide)
  (hv : v ∉ lpReplicaCurrentLeftSide)
  (huv : CurrentConnected (lpReplicaCurrentGraph G sites) n u v) :
-- imply
  ∃ i : I, 0 < n (lpReplicaCurrentSeamEdge sites i) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrent_exists_positiveSeam_of_crossConnection G sites n hu hv huv

/--
[lpReplicaCurrent_exists_connectedSeam_of_crossConnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCutParity.lean)
-/
@[path]
private lemma lpReplicaCurrent_exists_connectedSeam_of_crossConnection_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {n : Current (LPReplicaCurrentVertex V)}
  {u v : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (hu : u ∈ lpReplicaCurrentLeftSide)
  (hv : v ∉ lpReplicaCurrentLeftSide)
  (huv : CurrentConnected (lpReplicaCurrentGraph G sites) n u v) :
-- imply
  ∃ i : I, CurrentConnected (lpReplicaCurrentGraph G sites) n (lpReplicaCurrentLeft sites i) (lpReplicaCurrentRight sites i) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrent_exists_connectedSeam_of_crossConnection G sites n hu hv huv

/--
[lpReplicaCurrent_exists_connectedSeam_of_odd_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCutParity.lean)
-/
@[path]
private lemma lpReplicaCurrent_exists_connectedSeam_of_odd_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hodd : Odd (#(StatMech.Sharpness.sources (lpReplicaCurrentGraph G sites) (ofEdgeFun (lpReplicaCurrentGraph G sites) m) ∩ lpReplicaCurrentLeftSide))) :
-- imply
  ∃ i : I, CurrentConnected (lpReplicaCurrentGraph G sites) (ofEdgeFun (lpReplicaCurrentGraph G sites) m) (lpReplicaCurrentLeft sites i) (lpReplicaCurrentRight sites i) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrent_exists_connectedSeam_of_odd_sources G sites m hodd

/--
[lpReplicaCurrent_exists_positiveSeam_of_odd_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCutParity.lean)
-/
@[path]
private lemma lpReplicaCurrent_exists_positiveSeam_of_odd_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hodd : Odd (#(StatMech.Sharpness.sources (lpReplicaCurrentGraph G sites) (ofEdgeFun (lpReplicaCurrentGraph G sites) m) ∩ lpReplicaCurrentLeftSide))) :
-- imply
  ∃ i : I, 0 < (ofEdgeFun (lpReplicaCurrentGraph G sites) m) (lpReplicaCurrentSeamEdge sites i) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrent_exists_positiveSeam_of_odd_sources G sites m hodd

/--
[lpReplica_offdiagSource_inter_leftSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCutParity.lean)
-/
@[path]
private lemma lpReplica_offdiagSource_inter_leftSide_eq
  [Fintype V]
  [DecidableEq V]
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j) :
-- imply
  ((lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) ∩ lpReplicaCurrentLeftSide) = {lpReplicaCurrentLeft sites i, lpReplicaCurrentLeft sites j, lpReplicaCurrentGhost0} := by
-- proof
  apply StatMech.Ising.lpReplica_offdiagSource_inter_leftSide sites hsite hij

/--
[lpReplica_offdiagSource_left_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCutParity.lean)
-/
@[path]
private lemma lpReplica_offdiagSource_left_odd_eq
  [Fintype V]
  [DecidableEq V]
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j) :
-- imply
  Odd (#((lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) ∩ lpReplicaCurrentLeftSide)) := by
-- proof
  apply StatMech.Ising.lpReplica_offdiagSource_left_odd sites hsite hij

/--
[lpReplicaCurrent_exists_connectedSeam_of_offdiagSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCutParity.lean)
-/
@[path]
private lemma lpReplicaCurrent_exists_connectedSeam_of_offdiagSource_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hsrc : StatMech.Sharpness.sources (lpReplicaCurrentGraph G sites) (ofEdgeFun (lpReplicaCurrentGraph G sites) m) = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) :
-- imply
  ∃ k : I, CurrentConnected (lpReplicaCurrentGraph G sites) (ofEdgeFun (lpReplicaCurrentGraph G sites) m) (lpReplicaCurrentLeft sites k) (lpReplicaCurrentRight sites k) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrent_exists_connectedSeam_of_offdiagSource G sites hsite hij m hsrc

/--
[lpReplicaCurrent_exists_positiveSeam_of_offdiagSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCutParity.lean)
-/
@[path]
private lemma lpReplicaCurrent_exists_positiveSeam_of_offdiagSource_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hsrc : StatMech.Sharpness.sources (lpReplicaCurrentGraph G sites) (ofEdgeFun (lpReplicaCurrentGraph G sites) m) = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) :
-- imply
  ∃ k : I, 0 < (ofEdgeFun (lpReplicaCurrentGraph G sites) m) (lpReplicaCurrentSeamEdge sites k) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrent_exists_positiveSeam_of_offdiagSource G sites hsite hij m hsrc


-- created on 2026-10-23
