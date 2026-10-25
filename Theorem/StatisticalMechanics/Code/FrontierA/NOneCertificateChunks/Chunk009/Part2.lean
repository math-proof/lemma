/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk009.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk009.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts19_checked :
    rawMomentVCounts 19 = generatedVCounts19 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts19_checked :
    rawMomentQCounts 19 = generatedQCounts19 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients19_checked :
    rawMomentStateCoefficientList 19 = generatedStateCoefficients19 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts19_checked, qCounts19_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
