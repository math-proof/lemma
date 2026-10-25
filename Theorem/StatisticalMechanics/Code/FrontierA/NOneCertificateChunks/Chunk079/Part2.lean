/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk079.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk079.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts159_checked :
    rawMomentVCounts 159 = generatedVCounts159 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts159_checked :
    rawMomentQCounts 159 = generatedQCounts159 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients159_checked :
    rawMomentStateCoefficientList 159 = generatedStateCoefficients159 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts159_checked, qCounts159_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
