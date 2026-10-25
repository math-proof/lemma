/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingOneThermodynamicBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4DiagonalRate.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingBlockSource.Part2


namespace StatMech.FrontierD

noncomputable section

open Filter Topology


noncomputable def fkRectWindingBlockSource
    (k scale blocks leftRight cut : Nat)
    (hone : 1 <= leftRight) (hsep : leftRight < cut)
    (hleft : leftRight + 1 <
      (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val) (q a : Real) (ha : 0 < a)
    (hlower : ∀ xy ∈ connectionPathPairs (blocks + 1)
      (fkRectWindingBlockPathVertex k scale blocks cut x hx),
      a <= FK.twoPointFun
        (fkRectInducedGraph
          (fkRectWindingBlockVerticalFamily k scale blocks)
          (fkRectRightStripBand
            (fkRectWindingBlockVerticalFamily k scale blocks) cut 1
            ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)))
        (fkRectCriticalP q) q xy.1 xy.2) :
    FKRectWindingOneSource
      (fkRectWindingBlockVerticalFamily k scale blocks) q :=
  fkRectPathWindingOneSource
    (fkRectWindingBlockVerticalFamily k scale blocks) q leftRight cut
    hone hsep hleft x hx (blocks + 1)
    (fkRectWindingBlockPathVertex k scale blocks cut x hx)
    (fkRectWindingBlockPathVertex_first k scale blocks cut x hx)
    (fkRectWindingBlockPathVertex_last k scale blocks cut x hx)
    (by
      intro xy hxy
      apply reachable_of_twoPointFun_pos
      exact ha.trans_le (hlower xy hxy))

end
end StatMech.FrontierD
