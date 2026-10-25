/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk055.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk055.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts111_checked :
    rawMomentVCounts 111 = generatedVCounts111 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts111_checked :
    rawMomentQCounts 111 = generatedQCounts111 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients111_checked :
    rawMomentStateCoefficientList 111 = generatedStateCoefficients111 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts111_checked, qCounts111_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
