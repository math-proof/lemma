/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk239.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk239.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts479_checked :
    rawMomentVCounts 479 = generatedVCounts479 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts479_checked :
    rawMomentQCounts 479 = generatedQCounts479 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients479_checked :
    rawMomentStateCoefficientList 479 = generatedStateCoefficients479 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts479_checked, qCounts479_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
