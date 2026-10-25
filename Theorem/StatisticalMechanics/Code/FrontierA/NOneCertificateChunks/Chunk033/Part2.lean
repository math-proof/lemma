/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk033.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk033.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts67_checked :
    rawMomentVCounts 67 = generatedVCounts67 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts67_checked :
    rawMomentQCounts 67 = generatedQCounts67 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients67_checked :
    rawMomentStateCoefficientList 67 = generatedStateCoefficients67 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts67_checked, qCounts67_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
