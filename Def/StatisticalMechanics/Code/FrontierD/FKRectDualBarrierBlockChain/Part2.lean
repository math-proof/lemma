/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierBlockChain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierAuxiliary.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingBlockSource.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierBlockChain


namespace StatMech.FrontierD

noncomputable section

def fkRectWindingBlockColumnBulkPairs
    (k scale blocks right : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hxleft : 1 <= x.val) (hxright : x.val <= right) :=
  connectionPathPairs (blocks + 1)
    (fkRectWindingBlockColumnPathVertex k scale blocks right x
      hxleft hxright)


def fkRectWindingBlockColumnConnectorPairs
    (k scale blocks right : Nat)
    (hright : 1 <= right)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hxleft : 1 <= x.val) (hxright : x.val <= right) :
    Finset
      (FKRectColumnBandVertex
          (fkRectWindingBlockVerticalFamily k scale blocks)
          1 right 1
          ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1) ×
        FKRectColumnBandVertex
          (fkRectWindingBlockVerticalFamily k scale blocks)
          1 right 1
          ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)) :=
  { (fkRectColumnBandRowOne
        (fkRectWindingBlockVerticalFamily k scale blocks)
        1 right
        (fkRectUnitGapColumn
          (fkRectWindingBlockVerticalFamily k scale blocks))
        (by rfl) hright,
      fkRectColumnBandRowOne
        (fkRectWindingBlockVerticalFamily k scale blocks)
        1 right x hxleft hxright),
    (fkRectColumnBandLastRow
        (fkRectWindingBlockVerticalFamily k scale blocks)
        1 right x hxleft hxright,
      fkRectColumnBandLastRow
        (fkRectWindingBlockVerticalFamily k scale blocks)
        1 right
        (fkRectUnitGapColumn
          (fkRectWindingBlockVerticalFamily k scale blocks))
        (by rfl) hright) }


def fkRectWindingBlockColumnAuxiliaryPairs
    (k scale blocks right : Nat)
    (hright : 1 <= right)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hxleft : 1 <= x.val) (hxright : x.val <= right) :=
  fkRectWindingBlockColumnBulkPairs k scale blocks right x hxleft hxright ∪
    fkRectWindingBlockColumnConnectorPairs k scale blocks right hright x
      hxleft hxright

end
end StatMech.FrontierD
