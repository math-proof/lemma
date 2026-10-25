/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk225.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk225


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts450_checked :
    rawMomentVCounts 450 = generatedVCounts450 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts450_checked :
    rawMomentQCounts 450 = generatedQCounts450 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients450_checked :
    rawMomentStateCoefficientList 450 = generatedStateCoefficients450 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts450_checked, qCounts450_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
