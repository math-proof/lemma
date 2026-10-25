/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierNetObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualRankOneWinding
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierNetObstruction
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectDualBarrierNetObstructionVerticalAux
    (R : FKRectTorus) :
    (n : Nat) →
      (fkRectOpenGraph R
        (fkRectDualBarrierNetObstructionConfiguration R)).Walk
        (fkRectUnitGapColumn R, (⟨0, R.height_pos⟩ : Fin R.height))
        (fkRectUnitGapColumn R,
          (SixVertexArrows.cyclicPred R.height_pos)^[n]
            (⟨0, R.height_pos⟩ : Fin R.height))
  | 0 => .nil
  | n + 1 =>
      (fkRectDualBarrierNetObstructionVerticalAux R n).concat
        (by
          have h := fkRectDualBarrierNetObstruction_verticalAdj R
            ((SixVertexArrows.cyclicPred R.height_pos)^[n]
              (⟨0, R.height_pos⟩ : Fin R.height))
          simpa only [Function.iterate_succ_apply'] using h)

end
end StatMech.FrontierD
