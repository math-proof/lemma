import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitProfileTransferGraph.Part4
open StatMech StatMech.Ising


/--
[lpReplicaProfilePartialReflects_of_symmetrizedProfile_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitProfileTransferGraph.lean)
-/
@[path]
private lemma lpReplicaProfilePartialReflects_of_symmetrizedProfile_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m n q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (hn : lpReplicaSymmetrizedProfile G sites n = q) :
-- imply
  LPReplicaProfilePartialReflects G sites m n := by
-- proof
  apply StatMech.Ising.lpReplicaProfilePartialReflects_of_symmetrizedProfile_eq G sites m n q hm hn

/--
[lpReplicaProfilePartialReflects_commonOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitProfileTransferGraph.lean)
-/
@[path]
private lemma lpReplicaProfilePartialReflects_commonOrbit_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {m n : LPReplicaCommonOrbitProfile G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaProfilePartialReflects G sites m.1 n.1 := by
-- proof
  apply StatMech.Ising.lpReplicaProfilePartialReflects_commonOrbit G sites q m n

/--
[lpReplicaCommonOrbitTransferGraph_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitProfileTransferGraph.lean)
-/
@[path]
private lemma lpReplicaCommonOrbitTransferGraph_adj_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {m n : LPReplicaCommonOrbitProfile G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaCommonOrbitTransferGraph G sites q).Adj m n ↔ m ≠ n ∧ LPReplicaProfilePartialReflects G sites m.1 n.1 := by
-- proof
  apply StatMech.Ising.lpReplicaCommonOrbitTransferGraph_adj_iff G sites q m n

/--
[lpReplicaCommonOrbitTransferGraph_preconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitProfileTransferGraph.lean)
-/
@[path]
private lemma lpReplicaCommonOrbitTransferGraph_preconnected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaCommonOrbitTransferGraph G sites q).Preconnected := by
-- proof
  apply StatMech.Ising.lpReplicaCommonOrbitTransferGraph_preconnected G sites q

/--
[lpReplicaCommonOrbitTransferGraph_component_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitProfileTransferGraph.lean)
-/
@[path]
private lemma lpReplicaCommonOrbitTransferGraph_component_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {m n : LPReplicaCommonOrbitProfile G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaCommonOrbitTransferGraph G sites q).connectedComponentMk m = (lpReplicaCommonOrbitTransferGraph G sites q).connectedComponentMk n := by
-- proof
  apply StatMech.Ising.lpReplicaCommonOrbitTransferGraph_component_eq G sites q m n

/--
[lpReplicaOffdiag_source_target_transferComponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitProfileTransferGraph.lean)
-/
@[path]
private lemma lpReplicaOffdiag_source_target_transferComponent_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {y : LPReplicaOffdiagDecoratedTarget G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaOffdiagDecoratedSourceTransferComponent G sites i j q z = lpReplicaOffdiagDecoratedTargetTransferComponent G sites i j q y := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiag_source_target_transferComponent_eq G sites i j q z y

/--
[lpReplicaOffdiagDecoratedSource_card_eq_sum_transferComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitProfileTransferGraph.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_card_eq_sum_transferComponents_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) = ∑ c ∈ lpReplicaOffdiagBalancedRelevantTransferComponents G sites i j q, (lpReplicaOffdiagDecoratedSourcesInTransferComponent G sites i j q c).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_card_eq_sum_transferComponents G sites i j q

/--
[lpReplicaOffdiagBalancedOutputs_card_eq_sum_transferComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitProfileTransferGraph.lean)
-/
@[path]
private lemma lpReplicaOffdiagBalancedOutputs_card_eq_sum_transferComponents_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaOffdiagBalancedOutputs G sites i j q).card = ∑ c ∈ lpReplicaOffdiagBalancedRelevantTransferComponents G sites i j q, (lpReplicaOffdiagBalancedOutputsInTransferComponent G sites i j q c).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagBalancedOutputs_card_eq_sum_transferComponents G sites i j q

/--
[lpReplicaOffdiagOrbitAtomCardInequality_of_transferComponentCards](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitProfileTransferGraph.lean)
-/
@[path]
private lemma lpReplicaOffdiagOrbitAtomCardInequality_of_transferComponentCards_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : ∀ c ∈ lpReplicaOffdiagBalancedRelevantTransferComponents G sites i j q, (lpReplicaOffdiagDecoratedSourcesInTransferComponent G sites i j q c).card <= (lpReplicaOffdiagBalancedOutputsInTransferComponent G sites i j q c).card) :
-- imply
  LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagOrbitAtomCardInequality_of_transferComponentCards G sites i j q hcard


-- created on 2026-10-23
