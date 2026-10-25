import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateResidual.Part3
open StatMech StatMech.Ising


/--
[lpReplicaAggregateRankFiveResidualCapacity_iff_card_le_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateResidual.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveResidualCapacity_iff_card_le_target_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  LPReplicaAggregateRankFiveResidualCapacity G sites q <-> Fintype.card (LPReplicaAggregateDecoratedSource G sites q) <= Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveResidualCapacity_iff_card_le_target G sites hsite q hcard

/--
[card_lpReplicaAggregateRankFiveHandledTargetImage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateResidual.lean)
-/
@[path]
private lemma card_lpReplicaAggregateRankFiveHandledTargetImage_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  (lpReplicaAggregateRankFiveHandledTargetImage G sites hsite q hcard).card = Fintype.card (LPReplicaAggregateLowOrResolvableHighSourceRankFive G sites q) := by
-- proof
  apply StatMech.Ising.card_lpReplicaAggregateRankFiveHandledTargetImage G sites hsite q hcard

/--
[lpReplicaAggregateRankFiveResidualCapacity_of_selected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateResidual.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveResidualCapacity_of_selected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hselected : LPReplicaAggregateRankFiveSelectedResidualCapacity G sites hsite q hcard) :
-- imply
  LPReplicaAggregateRankFiveResidualCapacity G sites q := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveResidualCapacity_of_selected G sites hsite q hcard hselected

/--
[lpReplicaAggregateProfileOrbitInequality_rankFive_of_residualCapacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateResidual.lean)
-/
@[path]
private lemma lpReplicaAggregateProfileOrbitInequality_rankFive_of_residualCapacity_eq
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
  (hJ : forall e, 0 <= J e)
  (hhf : forall x, 0 <= hf x)
  (hr : 0 <= r)
  (hresidual : forall q, Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5 -> LPReplicaAggregateRankFiveResidualCapacity G sites q)
  (hrank : forall q, Fintype.card (LPReplicaOrbitCommonSlot G sites q) ≠ 5 -> LPReplicaAggregateDecoratedInjection G sites q) :
-- imply
  LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateProfileOrbitInequality_rankFive_of_residualCapacity G sites hsite beta J hf r hbeta hJ hhf hr hresidual hrank


-- created on 2026-10-23
