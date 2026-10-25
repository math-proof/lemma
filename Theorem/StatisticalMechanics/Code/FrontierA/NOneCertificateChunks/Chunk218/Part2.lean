/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk218.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk218.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts437_checked :
    rawMomentVCounts 437 = generatedVCounts437 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts437_checked :
    rawMomentQCounts 437 = generatedQCounts437 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients437_checked :
    rawMomentStateCoefficientList 437 = generatedStateCoefficients437 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts437_checked, qCounts437_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
