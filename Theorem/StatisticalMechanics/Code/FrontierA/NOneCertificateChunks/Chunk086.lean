/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk086.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk086


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts172_checked :
    rawMomentVCounts 172 = generatedVCounts172 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts172_checked :
    rawMomentQCounts 172 = generatedQCounts172 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients172_checked :
    rawMomentStateCoefficientList 172 = generatedStateCoefficients172 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts172_checked, qCounts172_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
