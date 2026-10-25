/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk024.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk024.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts49_checked :
    rawMomentVCounts 49 = generatedVCounts49 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts49_checked :
    rawMomentQCounts 49 = generatedQCounts49 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients49_checked :
    rawMomentStateCoefficientList 49 = generatedStateCoefficients49 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts49_checked, qCounts49_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
