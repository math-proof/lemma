/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk108.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk108.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts217_checked :
    rawMomentVCounts 217 = generatedVCounts217 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts217_checked :
    rawMomentQCounts 217 = generatedQCounts217 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients217_checked :
    rawMomentStateCoefficientList 217 = generatedStateCoefficients217 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts217_checked, qCounts217_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
