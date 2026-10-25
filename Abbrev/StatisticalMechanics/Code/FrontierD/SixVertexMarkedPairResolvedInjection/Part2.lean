/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairResolvedInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part11
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairResolvedInjection


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexResolvedLoopMarkedPair
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat) :=
  Sigma fun decorated : SixVertexLoopDecoratedPair T left right =>
    Fin ((sixVertexLoopDecoratedPairTotalC decorated).choose k)


end
end StatMech.FrontierD
