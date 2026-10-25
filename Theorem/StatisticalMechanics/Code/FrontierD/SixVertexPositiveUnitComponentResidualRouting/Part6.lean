/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part8


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexHorizontalResidualGeometricCertificate

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
    hmiddle_pos hmiddle_lt grade}


theorem loopTarget_supported
    (certificate : SixVertexHorizontalResidualGeometricCertificate source) :
    SixVertexConfigurationPairTwoCycleFineRelated source.1.1
      certificate.loopTarget.1.1 := by
  cases certificate with
  | fullMask full =>
      exact sixVertexHorizontalDegreeTwoLoopSpliceTarget_supported source
        (sixVertexHorizontalDegreeTwoLoopFullUnitMaskSpliceKey source full)
  | resolvedCross cross =>
      exact sixVertexHorizontalDegreeTwoLoopSpliceTarget_supported source
        (sixVertexHorizontalDegreeTwoLoopResolvedUnitCrossSpliceKey source cross)
  | fineRelated target related => exact related

end SixVertexHorizontalResidualGeometricCertificate
end
end StatMech.FrontierD
