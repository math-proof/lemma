/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoComponentStrand.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part6
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit
open Finset
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

structure SixVertexPositiveUnitComponentOrbitBase
    (T : EvenTorus) (middle : Fin (T.width + 1)) (k : Nat) where
  first : SixVertexArrows T
  second : SixVertexArrows T
  firstIce : first.IceRule
  secondIce : second.IceRule
  degreeTwo : SixVertexLocallyDegreeTwo first second
  k_pos : 0 < k
  k_le_middle : k ≤ middle.val
  middle_add_k_le_width : middle.val + k ≤ T.width
  firstSector : sixVertexUpCount
    (svTorusVerticalRows T first (svFinLast T.height_pos)) = middle.val - k
  secondSector : sixVertexUpCount
    (svTorusVerticalRows T second (svFinLast T.height_pos)) = middle.val + k
  component_card :
    Fintype.card (SixVertexDisagreementComponent first second) = 2 * k
  component_charge : forall component :
      SixVertexDisagreementComponent first second,
    sixVertexDisagreementComponentCharge first second component = 1

end
end StatMech.FrontierD
