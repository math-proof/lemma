/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk173.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk173.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts347_checked :
    rawMomentVCounts 347 = generatedVCounts347 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts347_checked :
    rawMomentQCounts 347 = generatedQCounts347 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients347_checked :
    rawMomentStateCoefficientList 347 = generatedStateCoefficients347 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts347_checked, qCounts347_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
