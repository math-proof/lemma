/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk221.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk221.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts443_checked :
    rawMomentVCounts 443 = generatedVCounts443 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts443_checked :
    rawMomentQCounts 443 = generatedQCounts443 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients443_checked :
    rawMomentStateCoefficientList 443 = generatedStateCoefficients443 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts443_checked, qCounts443_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
