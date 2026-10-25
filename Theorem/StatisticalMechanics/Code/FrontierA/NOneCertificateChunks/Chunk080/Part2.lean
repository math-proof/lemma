/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk080.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk080.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts161_checked :
    rawMomentVCounts 161 = generatedVCounts161 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts161_checked :
    rawMomentQCounts 161 = generatedQCounts161 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients161_checked :
    rawMomentStateCoefficientList 161 = generatedStateCoefficients161 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts161_checked, qCounts161_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
