/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk178.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk178


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts356_checked :
    rawMomentVCounts 356 = generatedVCounts356 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts356_checked :
    rawMomentQCounts 356 = generatedQCounts356 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients356_checked :
    rawMomentStateCoefficientList 356 = generatedStateCoefficients356 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts356_checked, qCounts356_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
