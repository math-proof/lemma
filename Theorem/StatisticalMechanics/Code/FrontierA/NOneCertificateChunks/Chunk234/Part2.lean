/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk234.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk234.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts469_checked :
    rawMomentVCounts 469 = generatedVCounts469 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts469_checked :
    rawMomentQCounts 469 = generatedQCounts469 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients469_checked :
    rawMomentStateCoefficientList 469 = generatedStateCoefficients469 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts469_checked, qCounts469_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
