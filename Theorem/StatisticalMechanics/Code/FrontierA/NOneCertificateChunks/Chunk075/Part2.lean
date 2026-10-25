/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk075.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk075.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts151_checked :
    rawMomentVCounts 151 = generatedVCounts151 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts151_checked :
    rawMomentQCounts 151 = generatedQCounts151 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients151_checked :
    rawMomentStateCoefficientList 151 = generatedStateCoefficients151 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts151_checked, qCounts151_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
