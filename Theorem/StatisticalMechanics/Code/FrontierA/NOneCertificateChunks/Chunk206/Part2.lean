/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk206.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk206.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts413_checked :
    rawMomentVCounts 413 = generatedVCounts413 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts413_checked :
    rawMomentQCounts 413 = generatedQCounts413 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients413_checked :
    rawMomentStateCoefficientList 413 = generatedStateCoefficients413 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts413_checked, qCounts413_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
