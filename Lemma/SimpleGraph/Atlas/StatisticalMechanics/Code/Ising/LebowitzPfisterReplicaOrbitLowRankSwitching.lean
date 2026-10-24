import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitLowRankSwitching
open Finset StatMech StatMech.Ising


/--
[lpReplicaOffdiagOrbitAtomCardInequality_of_commonSlotCard_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitLowRankSwitching.lean)
-/
@[path]
private lemma lpReplicaOffdiagOrbitAtomCardInequality_of_commonSlotCard_le_four_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hle : Fintype.card (LPReplicaOrbitCommonSlot G sites q) <= 4) :
-- imply
  LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagOrbitAtomCardInequality_of_commonSlotCard_le_four G sites hsite hij q hle

/--
[lpReplicaAggregateDecoratedInjection_of_commonSlotCard_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitLowRankSwitching.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedInjection_of_commonSlotCard_le_four_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hle : Fintype.card (LPReplicaOrbitCommonSlot G sites q) <= 4) :
-- imply
  LPReplicaAggregateDecoratedInjection G sites q := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedInjection_of_commonSlotCard_le_four G sites hsite q hle

/--
[lpReplicaAggregateProfileOrbitInequalityAt_of_commonSlotCard_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitLowRankSwitching.lean)
-/
@[path]
private lemma lpReplicaAggregateProfileOrbitInequalityAt_of_commonSlotCard_le_four_eq
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
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hle : Fintype.card (LPReplicaOrbitCommonSlot G sites q) <= 4) :
-- imply
  LPReplicaAggregateProfileOrbitInequalityAt G sites beta J hf r q := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateProfileOrbitInequalityAt_of_commonSlotCard_le_four G sites hsite beta J hf r hbeta hJ hhf hr q hle

/--
[lpReplicaAggregateProfileOrbitInequality_of_highRankAtomCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitLowRankSwitching.lean)
-/
@[path]
private lemma lpReplicaAggregateProfileOrbitInequality_of_highRankAtomCard_eq
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
  (hhigh : forall q i j, i ≠ j -> 5 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q) -> LPReplicaOffdiagOrbitAtomCardInequality G sites i j q) :
-- imply
  LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateProfileOrbitInequality_of_highRankAtomCard G sites hsite beta J hf r hbeta hJ hhf hr hhigh

/--
[lpReplicaAggregateProfileOrbitInequality_of_highRankAggregateInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitLowRankSwitching.lean)
-/
@[path]
private lemma lpReplicaAggregateProfileOrbitInequality_of_highRankAggregateInjection_eq
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
  (hhigh : forall q, 5 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q) -> LPReplicaAggregateDecoratedInjection G sites q) :
-- imply
  LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateProfileOrbitInequality_of_highRankAggregateInjection G sites hsite beta J hf r hbeta hJ hhf hr hhigh

/--
[lpReplicaMatchingDisconn_le_of_highRankAtomCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitLowRankSwitching.lean)
-/
@[path]
private lemma lpReplicaMatchingDisconn_le_of_highRankAtomCard_eq
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
  (hhigh : forall q i j, i ≠ j -> 5 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q) -> LPReplicaOffdiagOrbitAtomCardInequality G sites i j q) :
-- imply
  let H := lpReplicaCurrentGraph G sites let Jr := lpReplicaCurrentCoupling J hf r sourcePairDisconnSum H beta Jr ∅ ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * lpMatchingDisconnTwo H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <= 2 * lpMatchingDisconnZero H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * lpMatchingDisconnOne H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplicaMatchingDisconn_le_of_highRankAtomCard G sites hsite beta J hf r hbeta hJ hhf hr hhigh

/--
[lpReplicaMatchingDisconn_le_of_highRankAggregateInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitLowRankSwitching.lean)
-/
@[path]
private lemma lpReplicaMatchingDisconn_le_of_highRankAggregateInjection_eq
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
  (hhigh : forall q, 5 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q) -> LPReplicaAggregateDecoratedInjection G sites q) :
-- imply
  let H := lpReplicaCurrentGraph G sites let Jr := lpReplicaCurrentCoupling J hf r sourcePairDisconnSum H beta Jr ∅ ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * lpMatchingDisconnTwo H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <= 2 * lpMatchingDisconnZero H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * lpMatchingDisconnOne H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplicaMatchingDisconn_le_of_highRankAggregateInjection G sites hsite beta J hf r hbeta hJ hhf hr hhigh

/--
[lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_highRankAggregateInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitLowRankSwitching.lean)
-/
@[path]
private lemma lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_highRankAggregateInjection_eq
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
  (hhigh : forall q, 5 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q) -> LPReplicaAggregateDecoratedInjection G sites q) :
-- imply
  let H := lpReplicaCurrentGraph G sites let Jr := lpReplicaCurrentCoupling J hf r (∑ i : I, ∑ j : I, lpMatchingFiveCurrentCoefficient H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 i j) <= 0 := by
-- proof
  apply StatMech.Ising.lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_highRankAggregateInjection G sites hsite beta J hf r hbeta hJ hhf hr hhigh


-- created on 2026-10-23
