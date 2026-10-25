/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk008.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk008.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts17_checked :
    rawMomentVCounts 17 = generatedVCounts17 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts17_checked :
    rawMomentQCounts 17 = generatedQCounts17 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients17_checked :
    rawMomentStateCoefficientList 17 = generatedStateCoefficients17 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts17_checked, qCounts17_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
