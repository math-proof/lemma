import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOffdiagSwitching.Part3
open Finset StatMech StatMech.Ising


/--
[lpReplicaCurrentEdgeFlux_ofEdgeFun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOffdiagSwitching.lean)
-/
@[path]
private lemma lpReplicaCurrentEdgeFlux_ofEdgeFun_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaCurrentEdgeFlux G sites (ofEdgeFun (lpReplicaCurrentGraph G sites) m) = m := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdgeFlux_ofEdgeFun G sites m

/--
[lpReplicaOffdiagSeamSelector_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOffdiagSwitching.lean)
-/
@[path]
private lemma lpReplicaOffdiagSeamSelector_positive_eq
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
  0 < (ofEdgeFun (lpReplicaCurrentGraph G sites) m) (lpReplicaCurrentSeamEdge sites (lpReplicaOffdiagSeamSelector G sites hsite i j hij (ofEdgeFun (lpReplicaCurrentGraph G sites) m))) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagSeamSelector_positive G sites hsite hij m hsrc

/--
[lpReplicaOffdiagSeamSelector_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOffdiagSwitching.lean)
-/
@[path]
private lemma lpReplicaOffdiagSeamSelector_connected_eq
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
  CurrentConnected (lpReplicaCurrentGraph G sites) (ofEdgeFun (lpReplicaCurrentGraph G sites) m) (lpReplicaCurrentLeft sites (lpReplicaOffdiagSeamSelector G sites hsite i j hij (ofEdgeFun (lpReplicaCurrentGraph G sites) m))) (lpReplicaCurrentRight sites (lpReplicaOffdiagSeamSelector G sites hsite i j hij (ofEdgeFun (lpReplicaCurrentGraph G sites) m))) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagSeamSelector_connected G sites hsite hij m hsrc

/--
[lp_gatedSourcePairSum_partition_fintype](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOffdiagSwitching.lean)
-/
@[path]
private lemma lp_gatedSourcePairSum_partition_fintype_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  [Fintype L]
  [DecidableEq L]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {beta : Real}
  {A B : Finset W}
  [DecidablePred P]
-- given
  (J : Sym2 W -> Real)
  (P : Current W -> Prop)
  (f : Current W -> L) :
-- imply
  gatedSourcePairSum G beta J A B P = ∑ l : L, gatedSourcePairSum G beta J A B (fun n => f n = l ∧ P n) := by
-- proof
  apply StatMech.Ising.lp_gatedSourcePairSum_partition_fintype G beta J A B P f

/--
[lpReplica_sourcePairDisconnSum_offdiag_eq_sum_slices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOffdiagSwitching.lean)
-/
@[path]
private lemma lpReplica_sourcePairDisconnSum_offdiag_eq_sum_slices_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {beta : Real}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (J : Sym2 (LPReplicaCurrentVertex V) -> Real) :
-- imply
  sourcePairDisconnSum (lpReplicaCurrentGraph G sites) beta J (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 = ∑ k : I, lpReplicaOffdiagDisconnSlice G sites hsite i j hij beta J k := by
-- proof
  apply StatMech.Ising.lpReplica_sourcePairDisconnSum_offdiag_eq_sum_slices G sites hsite hij beta J

/--
[lpReplica_sourcePairDisconnSum_offdiag_eq_sum_toggled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOffdiagSwitching.lean)
-/
@[path]
private lemma lpReplica_sourcePairDisconnSum_offdiag_eq_sum_toggled_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {beta : Real}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (J : Sym2 (LPReplicaCurrentVertex V) -> Real) :
-- imply
  let H := lpReplicaCurrentGraph G sites let A := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 sourcePairDisconnSum H beta J A ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 = ∑ k : I, gatedSourcePairSum H beta J (A ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k) (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k) (fun n => (lpReplicaOffdiagSeamSelector G sites hsite i j hij n = k ∧ ¬ CurrentConnected H n lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) ∧ CurrentConnected H n (lpReplicaCurrentLeft sites k) (lpReplicaCurrentRight sites k)) := by
-- proof
  apply StatMech.Ising.lpReplica_sourcePairDisconnSum_offdiag_eq_sum_toggled G sites hsite hij beta J


-- created on 2026-10-23
