/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk204.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk204


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts408_checked :
    rawMomentVCounts 408 = generatedVCounts408 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts408_checked :
    rawMomentQCounts 408 = generatedQCounts408 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients408_checked :
    rawMomentStateCoefficientList 408 = generatedStateCoefficients408 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts408_checked, qCounts408_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
