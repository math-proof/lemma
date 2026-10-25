/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedLoopBigradeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairResolvedInjection.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopPairBigrade.Part2
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexResolvedLoopBigradeBridge


namespace StatMech.FrontierD

noncomputable section

def sixVertexResolvedLoopMarkedPairBigrade
    {T : EvenTorus} {left right : Fin (T.width + 1)} {k : Nat}
    (decorated : SixVertexResolvedLoopMarkedPair T left right k) : Nat × Nat :=
  sixVertexLoopDecoratedPairBigrade decorated.1

end
end StatMech.FrontierD
