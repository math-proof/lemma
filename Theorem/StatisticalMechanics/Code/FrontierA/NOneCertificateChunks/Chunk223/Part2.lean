/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk223.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk223.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts447_checked :
    rawMomentVCounts 447 = generatedVCounts447 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts447_checked :
    rawMomentQCounts 447 = generatedQCounts447 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients447_checked :
    rawMomentStateCoefficientList 447 = generatedStateCoefficients447 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts447_checked, qCounts447_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
