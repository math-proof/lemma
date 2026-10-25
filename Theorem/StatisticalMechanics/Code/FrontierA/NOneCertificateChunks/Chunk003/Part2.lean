/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk003.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk003.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts7_checked :
    rawMomentVCounts 7 = generatedVCounts7 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts7_checked :
    rawMomentQCounts 7 = generatedQCounts7 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients7_checked :
    rawMomentStateCoefficientList 7 = generatedStateCoefficients7 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts7_checked, qCounts7_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
