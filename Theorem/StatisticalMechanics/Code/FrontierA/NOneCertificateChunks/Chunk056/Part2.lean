/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk056.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk056.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts113_checked :
    rawMomentVCounts 113 = generatedVCounts113 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts113_checked :
    rawMomentQCounts 113 = generatedQCounts113 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients113_checked :
    rawMomentStateCoefficientList 113 = generatedStateCoefficients113 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts113_checked, qCounts113_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
