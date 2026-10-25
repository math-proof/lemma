/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairResolvedInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part11
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairResolvedInjection


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexExplicitResolvedMarkedPair
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat) :=
  Sigma fun source : SixVertexExplicitMarkedDecoratedPair T left right k =>
    SixVertexExplicitMarkedResolution source.2


end
end StatMech.FrontierD
