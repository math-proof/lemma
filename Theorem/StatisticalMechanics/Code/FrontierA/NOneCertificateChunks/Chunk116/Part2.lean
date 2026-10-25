/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk116.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk116.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts233_checked :
    rawMomentVCounts 233 = generatedVCounts233 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts233_checked :
    rawMomentQCounts 233 = generatedQCounts233 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients233_checked :
    rawMomentStateCoefficientList 233 = generatedStateCoefficients233 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts233_checked, qCounts233_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
