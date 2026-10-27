import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching.Part7
open Finset StatMech StatMech.Ising


/--
[lpReplicaAggregateDecoratedSource_indices_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedSource_indices_ne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateDecoratedSource G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  z.1 ≠ z.2.1 := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedSource_indices_ne G sites q z

/--
[lpReplicaAggregateDecoratedSourceSelectedSeam_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedSourceSelectedSeam_connected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateDecoratedSource G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  StatMech.Sharpness.CurrentConnected (lpReplicaCurrentGraph G sites) (StatMech.Sharpness.ofEdgeFun (lpReplicaCurrentGraph G sites) z.2.2.2.1.1.1) (lpReplicaCurrentLeft sites (lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q z)) (lpReplicaCurrentRight sites (lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q z)) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedSourceSelectedSeam_connected G sites hsite q z

/--
[lpReplicaAggregateDecoratedSourceSelectedSeam_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedSourceSelectedSeam_positive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateDecoratedSource G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  0 < StatMech.Sharpness.ofEdgeFun (lpReplicaCurrentGraph G sites) z.2.2.2.1.1.1 (lpReplicaCurrentSeamEdge sites (lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q z)) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedSourceSelectedSeam_positive G sites hsite q z

/--
[lpReplicaAggregateDecoratedSourceSelectedSeam_exists_copy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedSourceSelectedSeam_exists_copy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateDecoratedSource G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  ∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.2.2.2.1.1.1, c.1.1 = lpReplicaCurrentSeamEdge sites (lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q z) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedSourceSelectedSeam_exists_copy G sites hsite q z

/--
[nonempty_lpReplicaAggregatePooledMatching_iff_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean)
-/
@[path]
private lemma nonempty_lpReplicaAggregatePooledMatching_iff_hall_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Nonempty (LPReplicaAggregatePooledMatching G sites hsite q) <-> LPReplicaAggregatePooledHall G sites hsite q := by
-- proof
  apply StatMech.Ising.nonempty_lpReplicaAggregatePooledMatching_iff_hall G sites hsite q

/--
[lpReplicaAggregateDecoratedInjection_of_pooledMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedInjection_of_pooledMatching_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {m : LPReplicaAggregatePooledMatching G sites hsite q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaAggregateDecoratedInjection G sites q := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedInjection_of_pooledMatching G sites hsite q m

/--
[lpReplicaAggregateProfileOrbitInequality_of_aggregatePooledHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean)
-/
@[path]
private lemma lpReplicaAggregateProfileOrbitInequality_of_aggregatePooledHall_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (hHall : ∀ q, LPReplicaAggregatePooledHall G sites hsite q) :
-- imply
  LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateProfileOrbitInequality_of_aggregatePooledHall G sites hsite beta J hf r hbeta hJ hhf hr hHall

/--
[lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_aggregatePooledHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean)
-/
@[path]
private lemma lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_aggregatePooledHall_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (hHall : ∀ q, LPReplicaAggregatePooledHall G sites hsite q) :
-- imply
  let H := lpReplicaCurrentGraph G sites let Jr := lpReplicaCurrentCoupling J hf r (∑ i : I, ∑ j : I, lpMatchingFiveCurrentCoefficient H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 i j) <= 0 := by
-- proof
  apply StatMech.Ising.lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_aggregatePooledHall G sites hsite beta J hf r hbeta hJ hhf hr hHall

/--
[nonempty_lpReplicaAggregateCrossToggleMatching_iff_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean)
-/
@[path]
private lemma nonempty_lpReplicaAggregateCrossToggleMatching_iff_hall_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Nonempty (LPReplicaAggregateCrossToggleMatching G sites q) <-> LPReplicaAggregateCrossToggleHall G sites q := by
-- proof
  apply StatMech.Ising.nonempty_lpReplicaAggregateCrossToggleMatching_iff_hall G sites q

/--
[lpReplicaAggregateDecoratedInjection_of_crossToggleMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedInjection_of_crossToggleMatching_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {m : LPReplicaAggregateCrossToggleMatching G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaAggregateDecoratedInjection G sites q := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedInjection_of_crossToggleMatching G sites q m

/--
[lpReplicaAggregateProfileOrbitInequality_of_aggregateCrossToggleHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean)
-/
@[path]
private lemma lpReplicaAggregateProfileOrbitInequality_of_aggregateCrossToggleHall_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (hHall : ∀ q, LPReplicaAggregateCrossToggleHall G sites q) :
-- imply
  LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateProfileOrbitInequality_of_aggregateCrossToggleHall G sites beta J hf r hbeta hJ hhf hr hHall

/--
[lpReplicaAggregateDecoratedInjection_of_connectedSeamHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedInjection_of_connectedSeamHall_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hHall : LPReplicaAggregateConnectedSeamHall G sites q) :
-- imply
  LPReplicaAggregateDecoratedInjection G sites q := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedInjection_of_connectedSeamHall G sites q hHall

/--
[lpReplicaAggregateProfileOrbitInequality_of_connectedSeamHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean)
-/
@[path]
private lemma lpReplicaAggregateProfileOrbitInequality_of_connectedSeamHall_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (hHall : ∀ q, LPReplicaAggregateConnectedSeamHall G sites q) :
-- imply
  LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateProfileOrbitInequality_of_connectedSeamHall G sites beta J hf r hbeta hJ hhf hr hHall

/--
[lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_connectedSeamHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean)
-/
@[path]
private lemma lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_connectedSeamHall_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (hHall : ∀ q, LPReplicaAggregateConnectedSeamHall G sites q) :
-- imply
  let H := lpReplicaCurrentGraph G sites let Jr := lpReplicaCurrentCoupling J hf r (∑ i : I, ∑ j : I, lpMatchingFiveCurrentCoefficient H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 i j) <= 0 := by
-- proof
  apply StatMech.Ising.lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_connectedSeamHall G sites beta J hf r hbeta hJ hhf hr hHall

/--
[lpReplicaAggregateSelectedSeamHall_iff_capacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean)
-/
@[path]
private lemma lpReplicaAggregateSelectedSeamHall_iff_capacity_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaAggregateSelectedSeamHall G sites hsite q <-> LPReplicaAggregateSelectedSeamCapacity G sites hsite q := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateSelectedSeamHall_iff_capacity G sites hsite q

/--
[lpReplicaAggregateSelectedSeamRelated_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean)
-/
@[path]
private lemma lpReplicaAggregateSelectedSeamRelated_connected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateDecoratedSource G sites q}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hrelated : LPReplicaAggregateSelectedSeamRelated G sites hsite q z y) :
-- imply
  LPReplicaAggregateConnectedSeamRelated G sites q z y := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateSelectedSeamRelated_connected G sites hsite q z y hrelated

/--
[lpReplicaAggregateConnectedSeamHall_of_selectedSeamHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean)
-/
@[path]
private lemma lpReplicaAggregateConnectedSeamHall_of_selectedSeamHall_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hHall : LPReplicaAggregateSelectedSeamHall G sites hsite q) :
-- imply
  LPReplicaAggregateConnectedSeamHall G sites q := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateConnectedSeamHall_of_selectedSeamHall G sites hsite q hHall

/--
[lpReplicaAggregateDecoratedInjection_of_selectedSeamCapacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedInjection_of_selectedSeamCapacity_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcapacity : LPReplicaAggregateSelectedSeamCapacity G sites hsite q) :
-- imply
  LPReplicaAggregateDecoratedInjection G sites q := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedInjection_of_selectedSeamCapacity G sites hsite q hcapacity

/--
[lpReplicaAggregateProfileOrbitInequality_of_selectedSeamCapacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean)
-/
@[path]
private lemma lpReplicaAggregateProfileOrbitInequality_of_selectedSeamCapacity_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (hcapacity : ∀ q, LPReplicaAggregateSelectedSeamCapacity G sites hsite q) :
-- imply
  LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateProfileOrbitInequality_of_selectedSeamCapacity G sites hsite beta J hf r hbeta hJ hhf hr hcapacity

/--
[lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_selectedSeamCapacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean)
-/
@[path]
private lemma lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_selectedSeamCapacity_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (hcapacity : ∀ q, LPReplicaAggregateSelectedSeamCapacity G sites hsite q) :
-- imply
  let H := lpReplicaCurrentGraph G sites let Jr := lpReplicaCurrentCoupling J hf r (∑ i : I, ∑ j : I, lpMatchingFiveCurrentCoefficient H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 i j) <= 0 := by
-- proof
  apply StatMech.Ising.lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_selectedSeamCapacity G sites hsite beta J hf r hbeta hJ hhf hr hcapacity

/--
[card_lpReplicaAggregateSelectedTargetFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean)
-/
@[path]
private lemma card_lpReplicaAggregateSelectedTargetFiber_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card {y : LPReplicaAggregateDecoratedTarget G sites q // y.2.1 = k} = ∑ j : I, 2 * Fintype.card (LPReplicaDecoratedOrbitAtom G sites (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k) (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) q) := by
-- proof
  apply StatMech.Ising.card_lpReplicaAggregateSelectedTargetFiber G sites q k

/--
[lpReplicaAggregateSelectedSeamCapacity_iff_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean)
-/
@[path]
private lemma lpReplicaAggregateSelectedSeamCapacity_iff_explicit_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaAggregateSelectedSeamCapacity G sites hsite q <-> forall k : I, Fintype.card {z : LPReplicaAggregateDecoratedSource G sites q // lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q z = k} <= ∑ j : I, 2 * Fintype.card (LPReplicaDecoratedOrbitAtom G sites (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k) (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) q) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateSelectedSeamCapacity_iff_explicit G sites hsite q


-- created on 2026-10-23
