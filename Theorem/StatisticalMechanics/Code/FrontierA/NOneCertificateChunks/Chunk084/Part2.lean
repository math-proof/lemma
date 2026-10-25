/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk084.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk084.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts169_checked :
    rawMomentVCounts 169 = generatedVCounts169 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts169_checked :
    rawMomentQCounts 169 = generatedQCounts169 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients169_checked :
    rawMomentStateCoefficientList 169 = generatedStateCoefficients169 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts169_checked, qCounts169_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
