/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk169.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk169


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts338_checked :
    rawMomentVCounts 338 = generatedVCounts338 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts338_checked :
    rawMomentQCounts 338 = generatedQCounts338 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients338_checked :
    rawMomentStateCoefficientList 338 = generatedStateCoefficients338 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts338_checked, qCounts338_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
