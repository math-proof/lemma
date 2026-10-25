/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk117.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk117


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts234_checked :
    rawMomentVCounts 234 = generatedVCounts234 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts234_checked :
    rawMomentQCounts 234 = generatedQCounts234 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients234_checked :
    rawMomentStateCoefficientList 234 = generatedStateCoefficients234 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts234_checked, qCounts234_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
