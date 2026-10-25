import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedComponentPartitionCore
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[graham_notConnComp_admissible_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponentPartitionCore.lean)
-/
@[path]
private lemma graham_notConnComp_admissible_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {g k l : V}
-- given
  (p q : ↥G.edgeFinset -> Nat)
  (hkl : k ≠ l)
  (hp : sources G (ofEdgeFun G p) = {k, l})
  (hq : sources G (ofEdgeFun G q) = ∅) :
-- imply
  notConnComp G (ofEdgeFun G (fun e => p e + q e)) g ∈ grahamAdmissibleComponentComplements g k l ↔ ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) g k := by
-- proof
  apply StatMech.FrontierA.graham_notConnComp_admissible_iff G p q hkl hp hq


-- created on 2026-10-23
