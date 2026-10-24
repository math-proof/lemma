import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamWeightedGateShift
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[currentConnected_add_of_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedGateShift.lean)
-/
@[path]
private lemma currentConnected_add_of_left_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {u v : V}
-- given
  (p q : G.edgeFinset -> Nat)
  (h : CurrentConnected G (ofEdgeFun G p) u v) :
-- imply
  CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) u v := by
-- proof
  apply StatMech.FrontierA.currentConnected_add_of_left G p q h

/--
[sourcePairDisconnSum_gate_shift_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedGateShift.lean)
-/
@[path]
private lemma sourcePairDisconnSum_gate_shift_left_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {B : Finset V}
  {u v m : V}
-- given
  (J : Sym2 V -> Real)
  (huv : u ≠ v) :
-- imply
  sourcePairDisconnSum G beta J {u, v} B u m = sourcePairDisconnSum G beta J {u, v} B v m := by
-- proof
  apply StatMech.FrontierA.sourcePairDisconnSum_gate_shift_left G beta J B huv


-- created on 2026-10-23
