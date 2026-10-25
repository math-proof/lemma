import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierBlockChain.Part2
open StatMech StatMech.FrontierD


/--
[fkRectWindingBlockColumnPathVertex_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierBlockChain.lean)
-/
@[path]
private lemma fkRectWindingBlockColumnPathVertex_first_eq
  {k scale blocks right : Nat}
  {x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width}
-- given
  (hxleft : 1 <= x.val)
  (hxright : x.val <= right) :
-- imply
  fkRectWindingBlockColumnPathVertex k scale blocks right x hxleft hxright 0 = fkRectColumnBandRowOne (fkRectWindingBlockVerticalFamily k scale blocks) 1 right x hxleft hxright := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlockColumnPathVertex_first k scale blocks right x hxleft hxright

/--
[fkRectWindingBlockColumnPathVertex_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierBlockChain.lean)
-/
@[path]
private lemma fkRectWindingBlockColumnPathVertex_last_eq
  {k scale blocks right : Nat}
  {x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width}
-- given
  (hxleft : 1 <= x.val)
  (hxright : x.val <= right) :
-- imply
  fkRectWindingBlockColumnPathVertex k scale blocks right x hxleft hxright (Fin.last (blocks + 1)) = fkRectColumnBandLastRow (fkRectWindingBlockVerticalFamily k scale blocks) 1 right x hxleft hxright := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlockColumnPathVertex_last k scale blocks right x hxleft hxright

/--
[fkRectWindingBlockColumnAuxiliaryPairs_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierBlockChain.lean)
-/
@[path]
private lemma fkRectWindingBlockColumnAuxiliaryPairs_card_le_eq
  {k scale blocks right : Nat}
  {x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width}
-- given
  (hright : 1 <= right)
  (hxleft : 1 <= x.val)
  (hxright : x.val <= right) :
-- imply
  (fkRectWindingBlockColumnAuxiliaryPairs k scale blocks right hright x hxleft hxright).card <= blocks + 3 := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlockColumnAuxiliaryPairs_card_le k scale blocks right hright x hxleft hxright

/--
[fkRectWindingBlockColumnAuxiliaryPairs_spans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierBlockChain.lean)
-/
@[path]
private lemma fkRectWindingBlockColumnAuxiliaryPairs_spans_eq
  {k scale blocks right : Nat}
  {x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width}
-- given
  (hright : 1 <= right)
  (hxleft : 1 <= x.val)
  (hxright : x.val <= right) :
-- imply
  FKRectColumnBandConnectionChainSpans (fkRectWindingBlockVerticalFamily k scale blocks) 1 right (fkRectUnitGapColumn (fkRectWindingBlockVerticalFamily k scale blocks)) (by rfl) hright (fkRectWindingBlockColumnAuxiliaryPairs k scale blocks right hright x hxleft hxright) := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlockColumnAuxiliaryPairs_spans k scale blocks right hright x hxleft hxright


-- created on 2026-10-23
