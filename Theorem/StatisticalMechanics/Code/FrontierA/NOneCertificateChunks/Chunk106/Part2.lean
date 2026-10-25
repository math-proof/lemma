/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk106.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk106.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts213_checked :
    rawMomentVCounts 213 = generatedVCounts213 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts213_checked :
    rawMomentQCounts 213 = generatedQCounts213 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients213_checked :
    rawMomentStateCoefficientList 213 = generatedStateCoefficients213 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts213_checked, qCounts213_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
