/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoComponentStrand.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part6
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit
open Finset
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexPositiveUnitComponentOrbitBase

variable {T : EvenTorus} {middle : Fin (T.width + 1)} {k : Nat}


def negativeComponents
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    {cardinality : Nat}
    (positive : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) cardinality) :
    Finset (SixVertexDisagreementComponent base.first base.second) :=
  positive.1ᶜ


def mask
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    {cardinality : Nat}
    (positive : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) cardinality) :
    SixVertexArrows T :=
  sixVertexDisagreementComponentSetMask base.first base.second
    (base.negativeComponents positive)

end SixVertexPositiveUnitComponentOrbitBase
end
end StatMech.FrontierD
