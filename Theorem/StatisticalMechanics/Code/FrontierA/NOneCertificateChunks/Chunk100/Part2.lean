/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk100.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk100.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts201_checked :
    rawMomentVCounts 201 = generatedVCounts201 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts201_checked :
    rawMomentQCounts 201 = generatedQCounts201 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients201_checked :
    rawMomentStateCoefficientList 201 = generatedStateCoefficients201 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts201_checked, qCounts201_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
