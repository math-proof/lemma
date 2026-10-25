/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk144.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk144.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts289_checked :
    rawMomentVCounts 289 = generatedVCounts289 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts289_checked :
    rawMomentQCounts 289 = generatedQCounts289 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients289_checked :
    rawMomentStateCoefficientList 289 = generatedStateCoefficients289 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts289_checked, qCounts289_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
