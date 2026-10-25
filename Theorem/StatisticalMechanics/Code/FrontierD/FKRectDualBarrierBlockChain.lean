/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierBlockChain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierAuxiliary.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingBlockSource.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierBlockChain


namespace StatMech.FrontierD

noncomputable section

theorem fkRectWindingBlockColumnPathVertex_first
    (k scale blocks right : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hxleft : 1 <= x.val) (hxright : x.val <= right) :
    fkRectWindingBlockColumnPathVertex k scale blocks right x
        hxleft hxright 0 =
      fkRectColumnBandRowOne
        (fkRectWindingBlockVerticalFamily k scale blocks)
        1 right x hxleft hxright := by
  apply Subtype.ext
  change (fkRectWindingBlockPathVertex
      k scale blocks 1 x hxleft 0).1 =
    (fkRectRightBandRowOne
      (fkRectWindingBlockVerticalFamily k scale blocks) 1 x hxleft).1
  exact congrArg Subtype.val
    (fkRectWindingBlockPathVertex_first k scale blocks 1 x hxleft)

theorem fkRectWindingBlockColumnPathVertex_last
    (k scale blocks right : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hxleft : 1 <= x.val) (hxright : x.val <= right) :
    fkRectWindingBlockColumnPathVertex k scale blocks right x
        hxleft hxright (Fin.last (blocks + 1)) =
      fkRectColumnBandLastRow
        (fkRectWindingBlockVerticalFamily k scale blocks)
        1 right x hxleft hxright := by
  apply Subtype.ext
  change (fkRectWindingBlockPathVertex
      k scale blocks 1 x hxleft (Fin.last (blocks + 1))).1 =
    (fkRectRightBandLastRow
      (fkRectWindingBlockVerticalFamily k scale blocks) 1 x hxleft).1
  exact congrArg Subtype.val
    (fkRectWindingBlockPathVertex_last k scale blocks 1 x hxleft)


end
end StatMech.FrontierD
