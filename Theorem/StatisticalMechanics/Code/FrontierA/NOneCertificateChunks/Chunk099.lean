/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk099.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk099


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts198_checked :
    rawMomentVCounts 198 = generatedVCounts198 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts198_checked :
    rawMomentQCounts 198 = generatedQCounts198 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients198_checked :
    rawMomentStateCoefficientList 198 = generatedStateCoefficients198 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts198_checked, qCounts198_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
