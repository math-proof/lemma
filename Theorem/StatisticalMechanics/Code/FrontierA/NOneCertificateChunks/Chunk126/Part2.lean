/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk126.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk126.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts253_checked :
    rawMomentVCounts 253 = generatedVCounts253 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts253_checked :
    rawMomentQCounts 253 = generatedQCounts253 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients253_checked :
    rawMomentStateCoefficientList 253 = generatedStateCoefficients253 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts253_checked, qCounts253_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
