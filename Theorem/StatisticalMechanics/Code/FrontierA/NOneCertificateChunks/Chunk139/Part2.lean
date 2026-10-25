/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk139.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk139.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts279_checked :
    rawMomentVCounts 279 = generatedVCounts279 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts279_checked :
    rawMomentQCounts 279 = generatedQCounts279 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients279_checked :
    rawMomentStateCoefficientList 279 = generatedStateCoefficients279 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts279_checked, qCounts279_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
