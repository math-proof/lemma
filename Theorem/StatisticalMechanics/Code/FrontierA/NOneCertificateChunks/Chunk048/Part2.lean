/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk048.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk048.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts97_checked :
    rawMomentVCounts 97 = generatedVCounts97 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts97_checked :
    rawMomentQCounts 97 = generatedQCounts97 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients97_checked :
    rawMomentStateCoefficientList 97 = generatedStateCoefficients97 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts97_checked, qCounts97_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
