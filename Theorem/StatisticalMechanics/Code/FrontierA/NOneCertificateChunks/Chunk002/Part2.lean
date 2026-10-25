/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk002.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk002.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts5_checked :
    rawMomentVCounts 5 = generatedVCounts5 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts5_checked :
    rawMomentQCounts 5 = generatedQCounts5 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients5_checked :
    rawMomentStateCoefficientList 5 = generatedStateCoefficients5 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts5_checked, qCounts5_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
