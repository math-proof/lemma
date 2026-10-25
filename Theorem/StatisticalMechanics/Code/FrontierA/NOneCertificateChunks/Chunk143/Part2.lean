/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk143.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk143.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts287_checked :
    rawMomentVCounts 287 = generatedVCounts287 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts287_checked :
    rawMomentQCounts 287 = generatedQCounts287 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients287_checked :
    rawMomentStateCoefficientList 287 = generatedStateCoefficients287 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts287_checked, qCounts287_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
