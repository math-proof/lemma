import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWSequentialStoppedExplorationBridge
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[RlcBookFaithfulExtremalTracePair.sequentialComparison_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedExplorationBridge.lean)
-/
@[path]
private lemma sequentialComparison_closed_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
-- given
  (hfaith : RlcBookFaithfulExtremalTracePair gamma gamma')
  (he : e ∈ rlc_sequentialExtremalExteriorEdges gamma gamma') :
-- imply
  rlc_sequentialExtremalClosedComparison gamma gamma' hfaith.toSequentialExplorationState.rawConfig e = false := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulExtremalTracePair.sequentialComparison_closed hfaith he

/--
[RlcBookFaithfulExtremalTracePair.sequentialComparison_agrees](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedExplorationBridge.lean)
-/
@[path]
private lemma sequentialComparison_agrees_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
-- given
  (hfaith : RlcBookFaithfulExtremalTracePair gamma gamma')
  (he : e ∉ rlc_sequentialExtremalExteriorEdges gamma gamma') :
-- imply
  rlc_sequentialExtremalClosedComparison gamma gamma' hfaith.toSequentialExplorationState.rawConfig e = hfaith.toSequentialExplorationState.rawConfig e := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulExtremalTracePair.sequentialComparison_agrees hfaith he


-- created on 2026-10-23
