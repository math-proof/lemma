/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk017.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk017.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts35_checked :
    rawMomentVCounts 35 = generatedVCounts35 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts35_checked :
    rawMomentQCounts 35 = generatedQCounts35 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients35_checked :
    rawMomentStateCoefficientList 35 = generatedStateCoefficients35 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts35_checked, qCounts35_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
