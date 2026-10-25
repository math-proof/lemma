/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk192.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk192.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts385_checked :
    rawMomentVCounts 385 = generatedVCounts385 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts385_checked :
    rawMomentQCounts 385 = generatedQCounts385 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients385_checked :
    rawMomentStateCoefficientList 385 = generatedStateCoefficients385 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts385_checked, qCounts385_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
