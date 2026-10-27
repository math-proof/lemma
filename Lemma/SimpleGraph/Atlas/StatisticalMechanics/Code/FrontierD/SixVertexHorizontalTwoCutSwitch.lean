import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalTwoCutSwitch.Part2
open StatMech StatMech.FrontierD


/--
[sixVertexHorizontalTwoCutMask_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalTwoCutSwitch.lean)
-/
@[path]
private lemma sixVertexHorizontalTwoCutMask_boundary_eq
  {T : EvenTorus}
  {a b : Fin T.width}
  {x : Fin T.width}
-- given
  (hab : a.val < b.val) :
-- imply
  sixVertexHorizontalTwoCutMask a b (SixVertexArrows.cyclicPred T.width_pos x) ≠ sixVertexHorizontalTwoCutMask a b x ↔ x = a ∨ x = b := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalTwoCutMask_boundary hab x

/--
[sixVertexHorizontalTwoCutMask_sum_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalTwoCutSwitch.lean)
-/
@[path]
private lemma sixVertexHorizontalTwoCutMask_sum_boundary_eq
  {T : EvenTorus}
  {a b : Fin T.width}
-- given
  (hab : a.val < b.val)
  (f : T.Vertex -> Nat) :
-- imply
  (∑ v ∈ (Finset.univ : Finset T.Vertex).filter (fun v => sixVertexHorizontalTwoCutMask a b (SixVertexArrows.cyclicPred T.width_pos v.1) ≠ sixVertexHorizontalTwoCutMask a b v.1), f v) = (∑ j : Fin T.height, f (a, j)) + ∑ j : Fin T.height, f (b, j) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalTwoCutMask_sum_boundary hab f

/--
[sixVertexHorizontalTwoCutMask_boundaryBalanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalTwoCutSwitch.lean)
-/
@[path]
private lemma sixVertexHorizontalTwoCutMask_boundaryBalanced_eq
  {T : EvenTorus}
  {a b : Fin T.width}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
  (hab : a.val < b.val)
  (hbalanced : SixVertexHorizontalPairTwoCutBalanced horizontal a b) :
-- imply
  SixVertexHorizontalPairSwitchBoundaryBalanced (sixVertexHorizontalTwoCutMask a b) horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalTwoCutMask_boundaryBalanced horizontal hab hbalanced

/--
[sixVertexHorizontalTwoCutSwitch_bigrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalTwoCutSwitch.lean)
-/
@[path]
private lemma sixVertexHorizontalTwoCutSwitch_bigrade_eq
  {T : EvenTorus}
  {a b : Fin T.width}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
  (hab : a.val < b.val)
  (hbalanced : SixVertexHorizontalPairTwoCutBalanced horizontal a b) :
-- imply
  sixVertexHorizontalPairBigrade (sixVertexSwitchHorizontalPair (sixVertexHorizontalTwoCutMask a b) horizontal) = sixVertexHorizontalPairBigrade horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalTwoCutSwitch_bigrade horizontal hab hbalanced


-- created on 2026-10-23
