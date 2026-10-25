/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk251.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk251


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts502_checked :
    rawMomentVCounts 502 = generatedVCounts502 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts502_checked :
    rawMomentQCounts 502 = generatedQCounts502 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients502_checked :
    rawMomentStateCoefficientList 502 = generatedStateCoefficients502 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts502_checked, qCounts502_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
