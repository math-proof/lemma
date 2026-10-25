import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.Part4
open StatMech StatMech.Ising


/--
[LPReplicaAggregateRankFiveStrictRouteWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.lean)
-/
@[path]
private lemma LPReplicaAggregateRankFiveStrictRouteWeight_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  0 ≤ LPReplicaAggregateRankFiveStrictRouteWeight G sites hsite q hcard z y := by
-- proof
  apply StatMech.Ising.LPReplicaAggregateRankFiveStrictRouteWeight_nonneg G sites hsite q hcard z y

/--
[LPReplicaAggregateRankFiveStrictRouteWeight_eq_zero_of_not_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.lean)
-/
@[path]
private lemma LPReplicaAggregateRankFiveStrictRouteWeight_eq_zero_of_not_related_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hnot : ¬ LPReplicaAggregateRankFiveStrictRouteRelated G sites hsite q hcard z y) :
-- imply
  LPReplicaAggregateRankFiveStrictRouteWeight G sites hsite q hcard z y = 0 := by
-- proof
  apply StatMech.Ising.LPReplicaAggregateRankFiveStrictRouteWeight_eq_zero_of_not_related G sites hsite q hcard z y hnot

/--
[mem_LPReplicaAggregateRankFiveStrictRouteIncomingDegree_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.lean)
-/
@[path]
private lemma mem_LPReplicaAggregateRankFiveStrictRouteIncomingDegree_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {degree : Nat}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  z ∈ LPReplicaAggregateRankFiveStrictRouteIncomingDegree G sites hsite q hcard degree y ↔ LPReplicaAggregateRankFiveStrictRouteRelated G sites hsite q hcard z y ∧ (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z).card = degree := by
-- proof
  apply StatMech.Ising.mem_LPReplicaAggregateRankFiveStrictRouteIncomingDegree_iff G sites hsite q hcard degree y z

/--
[mem_LPReplicaAggregateRankFiveStrictRouteIncoming_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.lean)
-/
@[path]
private lemma mem_LPReplicaAggregateRankFiveStrictRouteIncoming_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  z ∈ LPReplicaAggregateRankFiveStrictRouteIncoming G sites hsite q hcard y ↔ LPReplicaAggregateRankFiveStrictRouteRelated G sites hsite q hcard z y := by
-- proof
  apply StatMech.Ising.mem_LPReplicaAggregateRankFiveStrictRouteIncoming_iff G sites hsite q hcard y z

/--
[LPReplicaAggregateRankFiveStrictRouteIncomingDegree_subset_incoming](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.lean)
-/
@[path]
private lemma LPReplicaAggregateRankFiveStrictRouteIncomingDegree_subset_incoming_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {degree : Nat}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  LPReplicaAggregateRankFiveStrictRouteIncomingDegree G sites hsite q hcard degree y ⊆ LPReplicaAggregateRankFiveStrictRouteIncoming G sites hsite q hcard y := by
-- proof
  apply StatMech.Ising.LPReplicaAggregateRankFiveStrictRouteIncomingDegree_subset_incoming G sites hsite q hcard degree y

/--
[LPReplicaAggregateRankFiveStrictRouteIncoming_card_le_candidates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.lean)
-/
@[path]
private lemma LPReplicaAggregateRankFiveStrictRouteIncoming_card_le_candidates_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
  {d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z)}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hzd : lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget G sites hsite q hcard z d = y) :
-- imply
  (LPReplicaAggregateRankFiveStrictRouteIncoming G sites hsite q hcard y).card ≤ (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z).card := by
-- proof
  apply StatMech.Ising.LPReplicaAggregateRankFiveStrictRouteIncoming_card_le_candidates G sites hsite q hcard y z d hzd

/--
[LPReplicaAggregateRankFiveStrictRouteWeight_sum_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.lean)
-/
@[path]
private lemma LPReplicaAggregateRankFiveStrictRouteWeight_sum_target_eq
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
  ∑ y : LPReplicaAggregateDecoratedTarget G sites q, LPReplicaAggregateRankFiveStrictRouteWeight G sites hsite q hcard z y = 1 := by
-- proof
  apply StatMech.Ising.LPReplicaAggregateRankFiveStrictRouteWeight_sum_target G sites hsite q hcard z

/--
[LPReplicaAggregateRankFiveStrictRouteWeight_sum_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.lean)
-/
@[path]
private lemma LPReplicaAggregateRankFiveStrictRouteWeight_sum_source_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  (∑ z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q, LPReplicaAggregateRankFiveStrictRouteWeight G sites hsite q hcard z y) = ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree G sites hsite q hcard 1 y).card : Real) + ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree G sites hsite q hcard 2 y).card : Real) / 2 := by
-- proof
  apply StatMech.Ising.LPReplicaAggregateRankFiveStrictRouteWeight_sum_source G sites hsite q hcard y

/--
[LPReplicaAggregateRankFiveStrictRouteTargetLoad_iff_integer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.lean)
-/
@[path]
private lemma LPReplicaAggregateRankFiveStrictRouteTargetLoad_iff_integer_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  LPReplicaAggregateRankFiveStrictRouteTargetLoad G sites hsite q hcard ↔ ∀ y : LPReplicaAggregateDecoratedTarget G sites q, 2 * (LPReplicaAggregateRankFiveStrictRouteIncomingDegree G sites hsite q hcard 1 y).card + (LPReplicaAggregateRankFiveStrictRouteIncomingDegree G sites hsite q hcard 2 y).card ≤ 2 := by
-- proof
  apply StatMech.Ising.LPReplicaAggregateRankFiveStrictRouteTargetLoad_iff_integer G sites hsite q hcard

/--
[LPReplicaAggregateRankFiveStrictRouteTargetLoad_iff_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.lean)
-/
@[path]
private lemma LPReplicaAggregateRankFiveStrictRouteTargetLoad_iff_classification_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  LPReplicaAggregateRankFiveStrictRouteTargetLoad G sites hsite q hcard ↔ ∀ y : LPReplicaAggregateDecoratedTarget G sites q, ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree G sites hsite q hcard 1 y).card = 0 ∧ (LPReplicaAggregateRankFiveStrictRouteIncomingDegree G sites hsite q hcard 2 y).card ≤ 2) ∨ ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree G sites hsite q hcard 1 y).card = 1 ∧ (LPReplicaAggregateRankFiveStrictRouteIncomingDegree G sites hsite q hcard 2 y).card = 0) := by
-- proof
  apply StatMech.Ising.LPReplicaAggregateRankFiveStrictRouteTargetLoad_iff_classification G sites hsite q hcard

/--
[LPReplicaAggregateRankFiveStrictRouteIncoming_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.lean)
-/
@[path]
private lemma LPReplicaAggregateRankFiveStrictRouteIncoming_classification_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree G sites hsite q hcard 1 y).card = 0 ∧ (LPReplicaAggregateRankFiveStrictRouteIncomingDegree G sites hsite q hcard 2 y).card ≤ 2) ∨ ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree G sites hsite q hcard 1 y).card = 1 ∧ (LPReplicaAggregateRankFiveStrictRouteIncomingDegree G sites hsite q hcard 2 y).card = 0) := by
-- proof
  apply StatMech.Ising.LPReplicaAggregateRankFiveStrictRouteIncoming_classification G sites hsite q hcard y

/--
[lpReplicaAggregateRankFiveStrictRouteTargetLoad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveStrictRouteTargetLoad_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  LPReplicaAggregateRankFiveStrictRouteTargetLoad G sites hsite q hcard := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveStrictRouteTargetLoad G sites hsite q hcard

/--
[LPReplicaAggregateRankFiveStrictRouteHall_of_targetLoad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.lean)
-/
@[path]
private lemma LPReplicaAggregateRankFiveStrictRouteHall_of_targetLoad_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hload : LPReplicaAggregateRankFiveStrictRouteTargetLoad G sites hsite q hcard) :
-- imply
  ∀ sources : Finset (LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q), sources.card ≤ (Finset.univ.filter fun target : LPReplicaAggregateDecoratedTarget G sites q => ∃ source ∈ sources, LPReplicaAggregateRankFiveStrictRouteRelated G sites hsite q hcard source target).card := by
-- proof
  apply StatMech.Ising.LPReplicaAggregateRankFiveStrictRouteHall_of_targetLoad G sites hsite q hcard hload

/--
[LPReplicaAggregateRankFiveStrictRouteHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.lean)
-/
@[path]
private lemma LPReplicaAggregateRankFiveStrictRouteHall_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  ∀ sources : Finset (LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q), sources.card ≤ (Finset.univ.filter fun target : LPReplicaAggregateDecoratedTarget G sites q => ∃ source ∈ sources, LPReplicaAggregateRankFiveStrictRouteRelated G sites hsite q hcard source target).card := by
-- proof
  apply StatMech.Ising.LPReplicaAggregateRankFiveStrictRouteHall G sites hsite q hcard


-- created on 2026-10-23
