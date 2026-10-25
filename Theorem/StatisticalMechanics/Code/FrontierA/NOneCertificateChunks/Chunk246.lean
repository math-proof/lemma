/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk246.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk246


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts492_checked :
    rawMomentVCounts 492 = generatedVCounts492 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts492_checked :
    rawMomentQCounts 492 = generatedQCounts492 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients492_checked :
    rawMomentStateCoefficientList 492 = generatedStateCoefficients492 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts492_checked, qCounts492_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
