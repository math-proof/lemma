/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk167.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk167.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts335_checked :
    rawMomentVCounts 335 = generatedVCounts335 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts335_checked :
    rawMomentQCounts 335 = generatedQCounts335 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients335_checked :
    rawMomentStateCoefficientList 335 = generatedStateCoefficients335 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts335_checked, qCounts335_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
