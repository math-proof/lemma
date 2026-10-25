import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedBridgeGap
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[sourcePairDisconnSum_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedBridgeGap.lean)
-/
@[path]
private lemma sourcePairDisconnSum_comm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A B : Finset V}
  {u v : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  sourcePairDisconnSum G beta J A B u v = sourcePairDisconnSum G beta J A B v u := by
-- proof
  apply StatMech.FrontierA.sourcePairDisconnSum_comm G beta J A B u v

/--
[pairSources_symmDiff_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedBridgeGap.lean)
-/
@[path]
private lemma pairSources_symmDiff_bridge_eq
  [Fintype V]
  [DecidableEq V]
  {i k m : V}
-- given
  (hik : i ≠ k)
  (him : i ≠ m)
  (hkm : k ≠ m) :
-- imply
  ({i, k} : Finset V) ∆ {i, m} = {k, m} := by
-- proof
  apply StatMech.FrontierA.pairSources_symmDiff_bridge hik him hkm

/--
[expectationBridgeGap_eq_sourcePairDisconn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedBridgeGap.lean)
-/
@[path]
private lemma expectationBridgeGap_eq_sourcePairDisconn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i k m : V}
-- given
  (J : Sym2 V -> Real)
  (hik : i ≠ k)
  (him : i ≠ m)
  (hkm : k ≠ m) :
-- imply
  expectationJ G beta J {i, k} - expectationJ G beta J {i, m} * expectationJ G beta J {m, k} = sourcePairDisconnSum G beta J {i, k} ∅ i m / currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.expectationBridgeGap_eq_sourcePairDisconn G beta J hik him hkm

/--
[auxiliaryConnectionMass_div_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedBridgeGap.lean)
-/
@[path]
private lemma auxiliaryConnectionMass_div_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j m : V}
-- given
  (J : Sym2 V -> Real)
  (hij : i ≠ j)
  (him : i ≠ m)
  (hjm : j ≠ m) :
-- imply
  StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} ∅ i m / currentSum G beta J ∅ ^ 2 = expectationJ G beta J {i, m} * expectationJ G beta J {j, m} := by
-- proof
  apply StatMech.FrontierA.auxiliaryConnectionMass_div_eq G beta J hij him hjm


-- created on 2026-10-23
