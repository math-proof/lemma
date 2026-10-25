/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk092.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk092


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts184_checked :
    rawMomentVCounts 184 = generatedVCounts184 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts184_checked :
    rawMomentQCounts 184 = generatedQCounts184 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients184_checked :
    rawMomentStateCoefficientList 184 = generatedStateCoefficients184 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts184_checked, qCounts184_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
