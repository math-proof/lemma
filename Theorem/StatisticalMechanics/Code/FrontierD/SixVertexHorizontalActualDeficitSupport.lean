/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalActualDeficitSupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileDeficitSupport
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalActualDeficitSupport
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem card_sixVertexHorizontalPairProfileFiber
    (T : EvenTorus) (grade : Nat × Nat)
    (profile : SixVertexHorizontalPairCompletionProfile T) :
    Fintype.card (SixVertexHorizontalPairProfileFiber T grade profile) =
      sixVertexHorizontalPairProfileMultiplicity T grade profile := by
  rfl

end
end StatMech.FrontierD
