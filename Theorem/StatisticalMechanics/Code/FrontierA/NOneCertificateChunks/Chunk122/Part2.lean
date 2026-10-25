/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk122.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk122.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts245_checked :
    rawMomentVCounts 245 = generatedVCounts245 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts245_checked :
    rawMomentQCounts 245 = generatedQCounts245 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients245_checked :
    rawMomentStateCoefficientList 245 = generatedStateCoefficients245 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts245_checked, qCounts245_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
