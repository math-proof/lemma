/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk072.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk072


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts144_checked :
    rawMomentVCounts 144 = generatedVCounts144 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts144_checked :
    rawMomentQCounts 144 = generatedQCounts144 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients144_checked :
    rawMomentStateCoefficientList 144 = generatedStateCoefficients144 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts144_checked, qCounts144_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
