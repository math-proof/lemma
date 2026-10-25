/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk084.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk084


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts168_checked :
    rawMomentVCounts 168 = generatedVCounts168 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts168_checked :
    rawMomentQCounts 168 = generatedQCounts168 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients168_checked :
    rawMomentStateCoefficientList 168 = generatedStateCoefficients168 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts168_checked, qCounts168_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
