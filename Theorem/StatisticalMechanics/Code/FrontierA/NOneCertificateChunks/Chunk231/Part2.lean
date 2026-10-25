/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk231.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk231.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts463_checked :
    rawMomentVCounts 463 = generatedVCounts463 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts463_checked :
    rawMomentQCounts 463 = generatedQCounts463 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients463_checked :
    rawMomentStateCoefficientList 463 = generatedStateCoefficients463 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts463_checked, qCounts463_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
