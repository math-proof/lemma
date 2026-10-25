/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk093.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk093.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts187_checked :
    rawMomentVCounts 187 = generatedVCounts187 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts187_checked :
    rawMomentQCounts 187 = generatedQCounts187 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients187_checked :
    rawMomentStateCoefficientList 187 = generatedStateCoefficients187 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts187_checked, qCounts187_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
