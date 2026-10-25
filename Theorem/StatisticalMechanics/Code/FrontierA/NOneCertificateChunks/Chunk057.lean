/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk057.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk057


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts114_checked :
    rawMomentVCounts 114 = generatedVCounts114 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts114_checked :
    rawMomentQCounts 114 = generatedQCounts114 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients114_checked :
    rawMomentStateCoefficientList 114 = generatedStateCoefficients114 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts114_checked, qCounts114_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
