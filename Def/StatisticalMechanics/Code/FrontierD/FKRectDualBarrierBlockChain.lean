/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierBlockChain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierAuxiliary.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingBlockSource.Part3


namespace StatMech.FrontierD

noncomputable section

def fkRectWindingBlockColumnPathVertex
    (k scale blocks right : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hxleft : 1 <= x.val) (hxright : x.val <= right)
    (i : Fin (blocks + 2)) :
    FKRectColumnBandVertex
      (fkRectWindingBlockVerticalFamily k scale blocks)
      1 right 1
      ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1) := by
  let v := fkRectWindingBlockPathVertex k scale blocks 1 x hxleft i
  exact ⟨v.1, ⟨v.2.1, hxright, v.2.2.1, v.2.2.2⟩⟩

end
end StatMech.FrontierD
