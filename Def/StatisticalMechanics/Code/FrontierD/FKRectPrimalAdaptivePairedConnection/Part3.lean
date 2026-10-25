/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalPairedConnection
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptivePairedConnection.Part3
open MeasureTheory SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

def fkRectPrimalPairedConnectionFactor
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (i : Fin R.height) : Real :=
  (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 (Site 2)))).real
      (FK.boxConnEvent 2 (R.width + R.height)
        (fkRectVertexBoxEmbedding R (fkRectLeftColumn R, i))
        (fkRectVertexBoxEmbedding R (fkRectRightColumn R, pair i)))

end
end StatMech.FrontierD
