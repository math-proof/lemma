/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk240.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk240.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts481_checked :
    rawMomentVCounts 481 = generatedVCounts481 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts481_checked :
    rawMomentQCounts 481 = generatedQCounts481 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients481_checked :
    rawMomentStateCoefficientList 481 = generatedStateCoefficients481 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts481_checked, qCounts481_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
