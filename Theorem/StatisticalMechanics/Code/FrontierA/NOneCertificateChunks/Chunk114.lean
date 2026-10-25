/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk114.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk114


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts228_checked :
    rawMomentVCounts 228 = generatedVCounts228 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts228_checked :
    rawMomentQCounts 228 = generatedQCounts228 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients228_checked :
    rawMomentStateCoefficientList 228 = generatedStateCoefficients228 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts228_checked, qCounts228_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
