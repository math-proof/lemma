/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk169.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk169.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts339_checked :
    rawMomentVCounts 339 = generatedVCounts339 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts339_checked :
    rawMomentQCounts 339 = generatedQCounts339 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients339_checked :
    rawMomentStateCoefficientList 339 = generatedStateCoefficients339 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts339_checked, qCounts339_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
