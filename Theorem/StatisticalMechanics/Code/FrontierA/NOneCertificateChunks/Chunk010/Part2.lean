/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk010.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk010.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts21_checked :
    rawMomentVCounts 21 = generatedVCounts21 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts21_checked :
    rawMomentQCounts 21 = generatedQCounts21 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients21_checked :
    rawMomentStateCoefficientList 21 = generatedStateCoefficients21 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts21_checked, qCounts21_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
