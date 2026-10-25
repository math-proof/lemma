/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk098.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk098.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts197_checked :
    rawMomentVCounts 197 = generatedVCounts197 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts197_checked :
    rawMomentQCounts 197 = generatedQCounts197 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients197_checked :
    rawMomentStateCoefficientList 197 = generatedStateCoefficients197 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts197_checked, qCounts197_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
