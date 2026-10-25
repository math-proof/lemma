/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk019.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk019.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts39_checked :
    rawMomentVCounts 39 = generatedVCounts39 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts39_checked :
    rawMomentQCounts 39 = generatedQCounts39 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients39_checked :
    rawMomentStateCoefficientList 39 = generatedStateCoefficients39 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts39_checked, qCounts39_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
