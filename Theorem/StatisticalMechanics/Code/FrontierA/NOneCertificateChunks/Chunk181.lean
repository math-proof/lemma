/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk181.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk181


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts362_checked :
    rawMomentVCounts 362 = generatedVCounts362 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts362_checked :
    rawMomentQCounts 362 = generatedQCounts362 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients362_checked :
    rawMomentStateCoefficientList 362 = generatedStateCoefficients362 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts362_checked, qCounts362_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
