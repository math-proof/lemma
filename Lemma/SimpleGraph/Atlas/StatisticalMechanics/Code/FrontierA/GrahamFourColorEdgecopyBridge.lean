import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamFourColorEdgecopyBridge
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamFourColorToSplit_of_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorEdgecopyBridge.lean)
-/
@[path]
private lemma grahamFourColorToSplit_of_partition_eq
  [Fintype V]
  [DecidableEq V]
  {q : GrahamFourColoring (Copy G total)}
-- given
  (total : G.edgeFinset -> Nat)
  (hq : q.IsPartition Finset.univ) :
-- imply
  (grahamFourColorToSplit G total q).1 = (profileFlux G total q.color1, profileFlux G total q.color2, profileFlux G total q.color3) := by
-- proof
  apply StatMech.FrontierA.grahamFourColorToSplit_of_partition total q hq

/--
[grahamFourColor_edgecopy_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorEdgecopyBridge.lean)
-/
@[path]
private lemma grahamFourColor_edgecopy_bridge_eq
  [Fintype V]
  [DecidableEq V]
  [AddCommMonoid M]
-- given
  (total : G.edgeFinset -> Nat)
  (Theta : (G.edgeFinset -> Nat) -> (G.edgeFinset -> Nat) -> (G.edgeFinset -> Nat) -> M) :
-- imply
  (∑ s : GrahamFourSplit G total, grahamFourSplitMultiplicityNat G total s • Theta s.1.1 s.1.2.1 s.1.2.2) = ∑ q ∈ grahamFourColorings (Finset.univ : Finset (Copy G total)), Theta (profileFlux G total q.color1) (profileFlux G total q.color2) (profileFlux G total q.color3) := by
-- proof
  apply StatMech.FrontierA.grahamFourColor_edgecopy_bridge total Theta


-- created on 2026-10-23
