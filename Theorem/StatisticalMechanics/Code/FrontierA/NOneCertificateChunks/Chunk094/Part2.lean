/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk094.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk094.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts189_checked :
    rawMomentVCounts 189 = generatedVCounts189 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts189_checked :
    rawMomentQCounts 189 = generatedQCounts189 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients189_checked :
    rawMomentStateCoefficientList 189 = generatedStateCoefficients189 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts189_checked, qCounts189_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
