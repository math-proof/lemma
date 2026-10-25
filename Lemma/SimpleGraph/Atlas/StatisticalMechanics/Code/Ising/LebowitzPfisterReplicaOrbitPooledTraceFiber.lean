import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber.Part4
open Finset StatMech StatMech.Ising


/--
[lpReplicaOffdiagPooledSource_card_eq_sum_intermediateFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledTraceFiber.lean)
-/
@[path]
private lemma lpReplicaOffdiagPooledSource_card_eq_sum_intermediateFibers_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) = ∑ u : LPReplicaOffdiagPooledIntermediateAtom G sites i j q, (lpReplicaOffdiagPooledSourceIntermediateFiber G sites hsite hij q u).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagPooledSource_card_eq_sum_intermediateFibers G sites hsite hij q

/--
[lpReplicaOffdiagPooledTarget_card_eq_sum_intermediateFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledTraceFiber.lean)
-/
@[path]
private lemma lpReplicaOffdiagPooledTarget_card_eq_sum_intermediateFibers_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) = ∑ u : LPReplicaOffdiagPooledIntermediateAtom G sites i j q, (lpReplicaOffdiagPooledTargetIntermediateFiber G sites i j q u).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagPooledTarget_card_eq_sum_intermediateFibers G sites i j q

/--
[lpReplicaOffdiagOrbitAtomCardInequality_of_pooledIntermediateInjections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledTraceFiber.lean)
-/
@[path]
private lemma lpReplicaOffdiagOrbitAtomCardInequality_of_pooledIntermediateInjections_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hinj : ∀ u : LPReplicaOffdiagPooledIntermediateAtom G sites i j q, ∃ move : {z // z ∈ lpReplicaOffdiagPooledSourceIntermediateFiber G sites hsite hij q u} -> {y // y ∈ lpReplicaOffdiagPooledTargetIntermediateFiber G sites i j q u}, Function.Injective move) :
-- imply
  LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagOrbitAtomCardInequality_of_pooledIntermediateInjections G sites hsite hij q hinj

/--
[lpReplicaOffdiagPooledSource_card_eq_sum_traceFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledTraceFiber.lean)
-/
@[path]
private lemma lpReplicaOffdiagPooledSource_card_eq_sum_traceFibers_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) = ∑ u : LPReplicaOffdiagPooledTraceIndex G sites q, (lpReplicaOffdiagPooledSourceTraceFiber G sites i j q u).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagPooledSource_card_eq_sum_traceFibers G sites i j q

/--
[lpReplicaOffdiagPooledTarget_card_eq_sum_traceFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledTraceFiber.lean)
-/
@[path]
private lemma lpReplicaOffdiagPooledTarget_card_eq_sum_traceFibers_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) = ∑ u : LPReplicaOffdiagPooledTraceIndex G sites q, (lpReplicaOffdiagPooledTargetTraceFiber G sites i j q u).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagPooledTarget_card_eq_sum_traceFibers G sites i j q

/--
[lpReplicaOffdiagPooledDecoratedCard_of_traceFiberCards](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledTraceFiber.lean)
-/
@[path]
private lemma lpReplicaOffdiagPooledDecoratedCard_of_traceFiberCards_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : ∀ u : LPReplicaOffdiagPooledTraceIndex G sites q, (lpReplicaOffdiagPooledSourceTraceFiber G sites i j q u).card <= (lpReplicaOffdiagPooledTargetTraceFiber G sites i j q u).card) :
-- imply
  Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <= Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagPooledDecoratedCard_of_traceFiberCards G sites i j q hcard

/--
[lpReplicaOffdiagOrbitAtomCardInequality_of_pooledTraceFiberInjections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledTraceFiber.lean)
-/
@[path]
private lemma lpReplicaOffdiagOrbitAtomCardInequality_of_pooledTraceFiberInjections_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hinj : ∀ u : LPReplicaOffdiagPooledTraceIndex G sites q, ∃ move : {z // z ∈ lpReplicaOffdiagPooledSourceTraceFiber G sites i j q u} -> {y // y ∈ lpReplicaOffdiagPooledTargetTraceFiber G sites i j q u}, Function.Injective move) :
-- imply
  LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagOrbitAtomCardInequality_of_pooledTraceFiberInjections G sites i j q hinj

/--
[card_lpReplicaAggregateDecoratedSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledTraceFiber.lean)
-/
@[path]
private lemma card_lpReplicaAggregateDecoratedSource_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaAggregateDecoratedSource G sites q) = ∑ i : I, ∑ j : I, if i = j then 0 else Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) := by
-- proof
  apply StatMech.Ising.card_lpReplicaAggregateDecoratedSource G sites q

/--
[card_lpReplicaAggregateDecoratedTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledTraceFiber.lean)
-/
@[path]
private lemma card_lpReplicaAggregateDecoratedTarget_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) = ∑ i : I, ∑ j : I, 2 * Fintype.card (LPReplicaDecoratedOrbitAtom G sites (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) q) := by
-- proof
  apply StatMech.Ising.card_lpReplicaAggregateDecoratedTarget G sites q

/--
[lpReplicaAggregateDecoratedCard_of_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledTraceFiber.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedCard_of_injection_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hinj : LPReplicaAggregateDecoratedInjection G sites q) :
-- imply
  Fintype.card (LPReplicaAggregateDecoratedSource G sites q) <= Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedCard_of_injection G sites q hinj

/--
[lpReplicaAggregateProfileOrbitInequality_of_aggregateDecoratedInjections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledTraceFiber.lean)
-/
@[path]
private lemma lpReplicaAggregateProfileOrbitInequality_of_aggregateDecoratedInjections_eq
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
  (hinj : ∀ q, LPReplicaAggregateDecoratedInjection G sites q) :
-- imply
  LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateProfileOrbitInequality_of_aggregateDecoratedInjections G sites beta J hf r hbeta hJ hhf hr hinj


-- created on 2026-10-23
