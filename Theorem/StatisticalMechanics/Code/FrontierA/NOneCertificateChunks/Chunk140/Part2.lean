/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk140.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk140.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts281_checked :
    rawMomentVCounts 281 = generatedVCounts281 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts281_checked :
    rawMomentQCounts 281 = generatedQCounts281 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients281_checked :
    rawMomentStateCoefficientList 281 = generatedStateCoefficients281 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts281_checked, qCounts281_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
