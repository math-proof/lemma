/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoComponentStrand.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part4
open Finset
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexPositiveUnitComponentOrbitBase

variable {T : EvenTorus} {middle : Fin (T.width + 1)} {k : Nat}


noncomputable def sourceComponentSeed
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (positive : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) (k + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (component : SixVertexDisagreementComponent base.first base.second) :
    SixVertexOrientedDisagreementDart
      (base.source positive hmiddle_pos hmiddle_lt).1.1
      (base.source positive hmiddle_pos hmiddle_lt).2.1 :=
  (sixVertexOrientedDisagreementDartEquivEdge
    (base.source positive hmiddle_pos hmiddle_lt).1.2.1
    (base.source positive hmiddle_pos hmiddle_lt).2.2.1
    (base.source_degreeTwo positive hmiddle_pos hmiddle_lt)).symm
      ⟨base.componentRepresentativeEdge component, by
        change sixVertexTorusEdgeDisagrees
          (sixVertexTorusSwitchFirst (base.mask positive)
            base.first base.second)
          (sixVertexTorusSwitchSecond (base.mask positive)
            base.first base.second)
          (base.componentRepresentativeEdge component)
        rw [sixVertexTorusEdgeDisagrees_pairSwitch_iff]
        exact base.componentRepresentativeEdge_disagrees component⟩


end SixVertexPositiveUnitComponentOrbitBase
end
end StatMech.FrontierD
