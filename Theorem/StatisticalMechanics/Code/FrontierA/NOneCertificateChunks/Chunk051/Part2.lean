/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk051.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk051.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts103_checked :
    rawMomentVCounts 103 = generatedVCounts103 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts103_checked :
    rawMomentQCounts 103 = generatedQCounts103 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients103_checked :
    rawMomentStateCoefficientList 103 = generatedStateCoefficients103 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts103_checked, qCounts103_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
