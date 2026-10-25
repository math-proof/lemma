/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk023.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk023.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts47_checked :
    rawMomentVCounts 47 = generatedVCounts47 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts47_checked :
    rawMomentQCounts 47 = generatedQCounts47 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients47_checked :
    rawMomentStateCoefficientList 47 = generatedStateCoefficients47 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts47_checked, qCounts47_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
