import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.Part4
open Finset StatMech StatMech.Ising


/--
[LPReplicaOffdiagDecoratedSource.resolvable_or_unmarkedSaturated_of_highRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.lean)
-/
@[path]
private lemma resolvable_or_unmarkedSaturated_of_highRow_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hhigh : LPReplicaOffdiagDecoratedSource.IsHighRowRankFive G sites i j q z) :
-- imply
  LPReplicaOffdiagDecoratedSource.IsResolvableHighRowRankFive G sites i j q z ∨ LPReplicaOffdiagDecoratedSource.IsUnmarkedSaturatedRankFive G sites i j q z := by
-- proof
  apply StatMech.Ising.LPReplicaOffdiagDecoratedSource.resolvable_or_unmarkedSaturated_of_highRow G sites i j q z hhigh

/--
[LPReplicaOffdiagDecoratedSource.low_or_resolvable_or_unmarkedSaturated_rankFive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.lean)
-/
@[path]
private lemma low_or_resolvable_or_unmarkedSaturated_rankFive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  LPReplicaOffdiagDecoratedSource.IsLowRowRankFive G sites i j q z ∨ LPReplicaOffdiagDecoratedSource.IsResolvableHighRowRankFive G sites i j q z ∨ LPReplicaOffdiagDecoratedSource.IsUnmarkedSaturatedRankFive G sites i j q z := by
-- proof
  apply StatMech.Ising.LPReplicaOffdiagDecoratedSource.low_or_resolvable_or_unmarkedSaturated_rankFive G sites hsite hij q hcard z

/--
[LPReplicaOffdiagDecoratedSource.isUnmarkedSaturatedRankFive_of_mem_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.lean)
-/
@[path]
private lemma isUnmarkedSaturatedRankFive_of_mem_complement_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hz : z ∈ lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive G sites i j q) :
-- imply
  LPReplicaOffdiagDecoratedSource.IsUnmarkedSaturatedRankFive G sites i j q z := by
-- proof
  apply StatMech.Ising.LPReplicaOffdiagDecoratedSource.isUnmarkedSaturatedRankFive_of_mem_complement G sites hsite hij q hcard z hz

/--
[lpReplicaAggregateDecoratedSourceSelectedSeam_ne_left_of_unmarkedSaturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedSourceSelectedSeam_ne_left_of_unmarkedSaturated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateDecoratedSource G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hz : LPReplicaOffdiagDecoratedSource.IsUnmarkedSaturatedRankFive G sites z.1 z.2.1 q z.2.2.2) :
-- imply
  lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q z ≠ z.1 := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedSourceSelectedSeam_ne_left_of_unmarkedSaturated G sites hsite q z hz

/--
[lpReplicaAggregateDecoratedSourceSelectedSeam_ne_right_of_unmarkedSaturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedSourceSelectedSeam_ne_right_of_unmarkedSaturated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateDecoratedSource G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hz : LPReplicaOffdiagDecoratedSource.IsUnmarkedSaturatedRankFive G sites z.1 z.2.1 q z.2.2.2) :
-- imply
  lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q z ≠ z.2.1 := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedSourceSelectedSeam_ne_right_of_unmarkedSaturated G sites hsite q z hz

/--
[card_lpReplicaAggregateUnmarkedSaturatedSourceRankFive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.lean)
-/
@[path]
private lemma card_lpReplicaAggregateUnmarkedSaturatedSourceRankFive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) = ∑ i : I, ∑ j : I, if i = j then 0 else (lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive G sites i j q).card := by
-- proof
  apply StatMech.Ising.card_lpReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q

/--
[LPReplicaAggregateUnmarkedSaturatedSourceRankFive.toAggregate_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.lean)
-/
@[path]
private lemma toAggregate_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Injective (LPReplicaAggregateUnmarkedSaturatedSourceRankFive.toAggregate G sites q) := by
-- proof
  apply StatMech.Ising.LPReplicaAggregateUnmarkedSaturatedSourceRankFive.toAggregate_injective G sites q

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked_eq
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
  let a := z.toAggregate G sites q lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q a ≠ a.1 ∧ lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q a ≠ a.2.1 := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked G sites hsite q hcard z

/--
[lpReplicaOffdiag_rankFive_handled_union_unmarkedSaturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.lean)
-/
@[path]
private lemma lpReplicaOffdiag_rankFive_handled_union_unmarkedSaturated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  z ∈ lpReplicaOffdiagLowOrResolvableHighSourcesRankFive G sites i j q ∨ z ∈ lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiag_rankFive_handled_union_unmarkedSaturated G sites i j q z

/--
[lpReplicaOffdiag_rankFive_card_handled_add_unmarkedSaturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.lean)
-/
@[path]
private lemma lpReplicaOffdiag_rankFive_card_handled_add_unmarkedSaturated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaOffdiagLowOrResolvableHighSourcesRankFive G sites i j q).card + (lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive G sites i j q).card = Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiag_rankFive_card_handled_add_unmarkedSaturated G sites i j q

/--
[card_lpReplicaAggregateDecoratedSource_rankFive_eq_handled_add_unmarked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.lean)
-/
@[path]
private lemma card_lpReplicaAggregateDecoratedSource_rankFive_eq_handled_add_unmarked_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaAggregateDecoratedSource G sites q) = Fintype.card (LPReplicaAggregateLowOrResolvableHighSourceRankFive G sites q) + Fintype.card (LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) := by
-- proof
  apply StatMech.Ising.card_lpReplicaAggregateDecoratedSource_rankFive_eq_handled_add_unmarked G sites q

/--
[lpReplicaOffdiag_rankFive_handled_disjoint_unmarkedSaturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.lean)
-/
@[path]
private lemma lpReplicaOffdiag_rankFive_handled_disjoint_unmarkedSaturated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Disjoint (lpReplicaOffdiagLowOrResolvableHighSourcesRankFive G sites i j q) (lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive G sites i j q) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiag_rankFive_handled_disjoint_unmarkedSaturated G sites i j q


-- created on 2026-10-23
