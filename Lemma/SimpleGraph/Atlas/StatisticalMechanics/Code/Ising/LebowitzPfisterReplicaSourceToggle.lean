import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaSourceToggle
open Finset StatMech StatMech.Ising


/--
[lpReplicaCurrent_left_ne_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSourceToggle.lean)
-/
@[path]
private lemma lpReplicaCurrent_left_ne_right_eq
  [Fintype V]
  [DecidableEq V]
  {i : I}
-- given
  (sites : I -> V) :
-- imply
  lpReplicaCurrentLeft sites i ≠ lpReplicaCurrentRight sites i := by
-- proof
  apply StatMech.Ising.lpReplicaCurrent_left_ne_right sites i

/--
[lpReplicaCurrent_pair_eq_seamSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSourceToggle.lean)
-/
@[path]
private lemma lpReplicaCurrent_pair_eq_seamSource_eq
  [Fintype V]
  [DecidableEq V]
  {i : I}
-- given
  (sites : I -> V) :
-- imply
  ({lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i} : Finset (LPReplicaCurrentVertex V)) = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i := by
-- proof
  apply StatMech.Ising.lpReplicaCurrent_pair_eq_seamSource sites i

/--
[lpReplica_gatedSourcePairSum_toggle_seam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSourceToggle.lean)
-/
@[path]
private lemma lpReplica_gatedSourcePairSum_toggle_seam_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {A B : Finset (LPReplicaCurrentVertex V)}
  {i : I}
  [DecidablePred P]
-- given
  (sites : I -> V)
  (J : Sym2 (LPReplicaCurrentVertex V) -> Real)
  (P : Current (LPReplicaCurrentVertex V) -> Prop) :
-- imply
  gatedSourcePairSum (lpReplicaCurrentGraph G sites) beta J A B (fun n => P n ∧ CurrentConnected (lpReplicaCurrentGraph G sites) n (lpReplicaCurrentLeft sites i) (lpReplicaCurrentRight sites i)) = gatedSourcePairSum (lpReplicaCurrentGraph G sites) beta J (A ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) (B ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) (fun n => P n ∧ CurrentConnected (lpReplicaCurrentGraph G sites) n (lpReplicaCurrentLeft sites i) (lpReplicaCurrentRight sites i)) := by
-- proof
  apply StatMech.Ising.lpReplica_gatedSourcePairSum_toggle_seam G sites beta J A B i P

/--
[lpReplica_gatedDisconn_toggle_seam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSourceToggle.lean)
-/
@[path]
private lemma lpReplica_gatedDisconn_toggle_seam_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {A B : Finset (LPReplicaCurrentVertex V)}
  {i : I}
-- given
  (sites : I -> V)
  (J : Sym2 (LPReplicaCurrentVertex V) -> Real) :
-- imply
  gatedSourcePairSum (lpReplicaCurrentGraph G sites) beta J A B (fun n => ¬ CurrentConnected (lpReplicaCurrentGraph G sites) n lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 ∧ CurrentConnected (lpReplicaCurrentGraph G sites) n (lpReplicaCurrentLeft sites i) (lpReplicaCurrentRight sites i)) = gatedSourcePairSum (lpReplicaCurrentGraph G sites) beta J (A ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) (B ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) (fun n => ¬ CurrentConnected (lpReplicaCurrentGraph G sites) n lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 ∧ CurrentConnected (lpReplicaCurrentGraph G sites) n (lpReplicaCurrentLeft sites i) (lpReplicaCurrentRight sites i)) := by
-- proof
  apply StatMech.Ising.lpReplica_gatedDisconn_toggle_seam G sites beta J A B i


-- created on 2026-10-23
