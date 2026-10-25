/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk086.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk086.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts173_checked :
    rawMomentVCounts 173 = generatedVCounts173 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts173_checked :
    rawMomentQCounts 173 = generatedQCounts173 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients173_checked :
    rawMomentStateCoefficientList 173 = generatedStateCoefficients173 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts173_checked, qCounts173_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
