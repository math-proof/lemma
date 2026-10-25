/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoComponentStrand.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part6
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part4
open Finset
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexPositiveUnitComponentOrbitBase

variable {T : EvenTorus} {middle : Fin (T.width + 1)} {k : Nat}


theorem componentRepresentativeEdge_disagrees
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (component : SixVertexDisagreementComponent base.first base.second) :
    sixVertexTorusEdgeDisagrees base.first base.second
      (base.componentRepresentativeEdge component) :=
  (Classical.choose_spec component.2).1

theorem componentRepresentativeEdge_component
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (component : SixVertexDisagreementComponent base.first base.second) :
    (sixVertexTorusDisagreementGraph base.first base.second).connectedComponentMk
        (base.componentRepresentativeEdge component) =
      component.1 :=
  (Classical.choose_spec component.2).2


end SixVertexPositiveUnitComponentOrbitBase
end
end StatMech.FrontierD
