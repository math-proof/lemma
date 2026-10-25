/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk253.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk253.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts507_checked :
    rawMomentVCounts 507 = generatedVCounts507 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts507_checked :
    rawMomentQCounts 507 = generatedQCounts507 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients507_checked :
    rawMomentStateCoefficientList 507 = generatedStateCoefficients507 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts507_checked, qCounts507_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
