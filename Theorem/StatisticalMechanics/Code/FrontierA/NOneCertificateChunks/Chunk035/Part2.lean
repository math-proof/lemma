/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk035.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk035.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts71_checked :
    rawMomentVCounts 71 = generatedVCounts71 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts71_checked :
    rawMomentQCounts 71 = generatedQCounts71 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients71_checked :
    rawMomentStateCoefficientList 71 = generatedStateCoefficients71 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts71_checked, qCounts71_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
