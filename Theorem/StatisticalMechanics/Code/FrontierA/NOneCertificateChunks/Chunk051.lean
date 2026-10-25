/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk051.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk051


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts102_checked :
    rawMomentVCounts 102 = generatedVCounts102 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts102_checked :
    rawMomentQCounts 102 = generatedQCounts102 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients102_checked :
    rawMomentStateCoefficientList 102 = generatedStateCoefficients102 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts102_checked, qCounts102_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
