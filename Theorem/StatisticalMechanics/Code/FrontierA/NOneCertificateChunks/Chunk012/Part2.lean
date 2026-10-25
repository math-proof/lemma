/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk012.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk012.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts25_checked :
    rawMomentVCounts 25 = generatedVCounts25 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts25_checked :
    rawMomentQCounts 25 = generatedQCounts25 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients25_checked :
    rawMomentStateCoefficientList 25 = generatedStateCoefficients25 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts25_checked, qCounts25_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
