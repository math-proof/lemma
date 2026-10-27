import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateStrictRoute.Part2
open StatMech StatMech.Ising


/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_labeledRoute_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateStrictRoute.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_labeledRoute_disconnected_eq
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
  let a := z.toAggregate G sites q let k := lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q a Nonempty (LPReplicaAggregateRankFiveStrictRouteData G sites q a k) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_labeledRoute_disconnected G sites hsite q hcard z

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteTarget_selectedSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateStrictRoute.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteTarget_selectedSeam_eq
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
  (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteTarget G sites hsite q hcard z).2.1 = lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q (z.toAggregate G sites q) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteTarget_selectedSeam G sites hsite q hcard z


-- created on 2026-10-23
