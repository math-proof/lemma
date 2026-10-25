/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk201.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk201.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts403_checked :
    rawMomentVCounts 403 = generatedVCounts403 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts403_checked :
    rawMomentQCounts 403 = generatedQCounts403 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients403_checked :
    rawMomentStateCoefficientList 403 = generatedStateCoefficients403 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts403_checked, qCounts403_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
