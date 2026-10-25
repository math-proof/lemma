/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk233.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk233.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts467_checked :
    rawMomentVCounts 467 = generatedVCounts467 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts467_checked :
    rawMomentQCounts 467 = generatedQCounts467 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients467_checked :
    rawMomentStateCoefficientList 467 = generatedStateCoefficients467 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts467_checked, qCounts467_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
