/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk068.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk068.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts137_checked :
    rawMomentVCounts 137 = generatedVCounts137 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts137_checked :
    rawMomentQCounts 137 = generatedQCounts137 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients137_checked :
    rawMomentStateCoefficientList 137 = generatedStateCoefficients137 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts137_checked, qCounts137_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
