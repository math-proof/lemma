/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk082.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk082.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts165_checked :
    rawMomentVCounts 165 = generatedVCounts165 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts165_checked :
    rawMomentQCounts 165 = generatedQCounts165 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients165_checked :
    rawMomentStateCoefficientList 165 = generatedStateCoefficients165 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts165_checked, qCounts165_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
