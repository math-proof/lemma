/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk174.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk174.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts349_checked :
    rawMomentVCounts 349 = generatedVCounts349 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts349_checked :
    rawMomentQCounts 349 = generatedQCounts349 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients349_checked :
    rawMomentStateCoefficientList 349 = generatedStateCoefficients349 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts349_checked, qCounts349_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
