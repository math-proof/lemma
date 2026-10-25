/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk227.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk227


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts454_checked :
    rawMomentVCounts 454 = generatedVCounts454 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts454_checked :
    rawMomentQCounts 454 = generatedQCounts454 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients454_checked :
    rawMomentStateCoefficientList 454 = generatedStateCoefficients454 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts454_checked, qCounts454_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
