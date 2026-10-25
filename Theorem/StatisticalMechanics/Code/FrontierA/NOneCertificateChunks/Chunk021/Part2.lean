/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk021.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk021.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts43_checked :
    rawMomentVCounts 43 = generatedVCounts43 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts43_checked :
    rawMomentQCounts 43 = generatedQCounts43 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients43_checked :
    rawMomentStateCoefficientList 43 = generatedStateCoefficients43 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts43_checked, qCounts43_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
