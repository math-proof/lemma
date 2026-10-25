/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk012.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk012


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts24_checked :
    rawMomentVCounts 24 = generatedVCounts24 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts24_checked :
    rawMomentQCounts 24 = generatedQCounts24 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients24_checked :
    rawMomentStateCoefficientList 24 = generatedStateCoefficients24 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts24_checked, qCounts24_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
