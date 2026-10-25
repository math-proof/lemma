/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoComponentStrand.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part5
open Finset
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexPositiveUnitComponentOrbitBase

variable {T : EvenTorus} {middle : Fin (T.width + 1)} {k : Nat}


def presentation
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :
    SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt
      (SixVertexDisagreementComponent base.first base.second) k where
  component_card := base.component_card
  sourceEmbedding := base.sourceEmbedding hmiddle_pos hmiddle_lt
  targetEmbedding := base.targetEmbedding
  related_iff := base.physicalRelated_iff hmiddle_pos hmiddle_lt


end SixVertexPositiveUnitComponentOrbitBase
end
end StatMech.FrontierD
