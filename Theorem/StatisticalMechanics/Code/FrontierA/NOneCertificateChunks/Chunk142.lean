/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk142.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk142


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts284_checked :
    rawMomentVCounts 284 = generatedVCounts284 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts284_checked :
    rawMomentQCounts 284 = generatedQCounts284 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients284_checked :
    rawMomentStateCoefficientList 284 = generatedStateCoefficients284 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts284_checked, qCounts284_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
