/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk083.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk083


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts166_checked :
    rawMomentVCounts 166 = generatedVCounts166 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts166_checked :
    rawMomentQCounts 166 = generatedQCounts166 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients166_checked :
    rawMomentStateCoefficientList 166 = generatedStateCoefficients166 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts166_checked, qCounts166_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
