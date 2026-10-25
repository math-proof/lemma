/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk022.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk022


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts44_checked :
    rawMomentVCounts 44 = generatedVCounts44 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts44_checked :
    rawMomentQCounts 44 = generatedQCounts44 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients44_checked :
    rawMomentStateCoefficientList 44 = generatedStateCoefficients44 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts44_checked, qCounts44_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
