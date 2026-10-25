/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk050.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk050.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts101_checked :
    rawMomentVCounts 101 = generatedVCounts101 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts101_checked :
    rawMomentQCounts 101 = generatedQCounts101 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients101_checked :
    rawMomentStateCoefficientList 101 = generatedStateCoefficients101 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts101_checked, qCounts101_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
