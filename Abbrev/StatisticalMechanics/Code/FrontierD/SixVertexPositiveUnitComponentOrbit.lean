/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoComponentStrand.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part6
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part2
open Finset
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexPositiveUnitComponentOrbitData

variable {T : EvenTorus} {middle : Fin (T.width + 1)}

abbrev Component (data : SixVertexPositiveUnitComponentOrbitData T middle) :=
  SixVertexDisagreementComponent data.base.first data.base.second

abbrev SourceLayer (data : SixVertexPositiveUnitComponentOrbitData T middle) :=
  BooleanLayer data.Component (data.k + 1)

abbrev TargetLayer (data : SixVertexPositiveUnitComponentOrbitData T middle) :=
  BooleanLayer data.Component data.k

end SixVertexPositiveUnitComponentOrbitData
end
end StatMech.FrontierD
