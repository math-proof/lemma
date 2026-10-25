/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part8


namespace StatMech.FrontierD

noncomputable section

structure SixVertexPositiveUnitComponentResidualMixedRouting
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  unit : SixVertexPositiveUnitComponentResidualOrbitCover T middle
    hmiddle_pos hmiddle_lt grade
  geometric : ∀ source :
    SixVertexPositiveUnitComponentResidualGeometricSources T middle
      hmiddle_pos hmiddle_lt grade,
    SixVertexHorizontalResidualGeometricSurplusRepair source.1
  high : ∀ source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
    hmiddle_pos hmiddle_lt grade,
    SixVertexHorizontalResidualHighGeometricSurplusRepair source
  decoder : SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade →
    Option (SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade)
  decode_unit : ∀ unitSource,
    decoder (unit.matching unitSource) = some unitSource.1
  decode_geometric : ∀ source,
    decoder (geometric source).target = some source.1
  decode_paired : ∀ highSource branch,
    decoder ((high highSource).target branch) = some highSource.1

end
end StatMech.FrontierD
