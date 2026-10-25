/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoComponentStrand.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part2
open Finset
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexPositiveUnitComponentOrbitBase

variable {T : EvenTorus} {middle : Fin (T.width + 1)} {k : Nat}


def sourceEmbedding
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :
    BooleanLayer (SixVertexDisagreementComponent base.first base.second)
        (k + 1) ↪
      SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt :=
  ⟨fun positive => base.source positive hmiddle_pos hmiddle_lt,
    base.source_injective hmiddle_pos hmiddle_lt⟩


def targetEmbedding
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k) :
    BooleanLayer (SixVertexDisagreementComponent base.first base.second) k ↪
      SixVertexConfigurationPhysicalTarget T middle :=
  ⟨base.target, base.target_injective⟩


end SixVertexPositiveUnitComponentOrbitBase
end
end StatMech.FrontierD
