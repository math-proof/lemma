/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk250.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk250.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts501_checked :
    rawMomentVCounts 501 = generatedVCounts501 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts501_checked :
    rawMomentQCounts 501 = generatedQCounts501 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients501_checked :
    rawMomentStateCoefficientList 501 = generatedStateCoefficients501 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts501_checked, qCounts501_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
