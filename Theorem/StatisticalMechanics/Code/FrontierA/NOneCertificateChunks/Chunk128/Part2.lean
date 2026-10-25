/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk128.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk128.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts257_checked :
    rawMomentVCounts 257 = generatedVCounts257 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts257_checked :
    rawMomentQCounts 257 = generatedQCounts257 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients257_checked :
    rawMomentStateCoefficientList 257 = generatedStateCoefficients257 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts257_checked, qCounts257_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
