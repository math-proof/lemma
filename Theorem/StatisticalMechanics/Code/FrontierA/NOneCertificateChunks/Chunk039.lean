/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk039.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk039


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts78_checked :
    rawMomentVCounts 78 = generatedVCounts78 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts78_checked :
    rawMomentQCounts 78 = generatedQCounts78 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients78_checked :
    rawMomentStateCoefficientList 78 = generatedStateCoefficients78 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts78_checked, qCounts78_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
