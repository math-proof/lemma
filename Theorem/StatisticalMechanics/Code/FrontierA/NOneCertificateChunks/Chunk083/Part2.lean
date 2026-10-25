/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk083.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk083.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts167_checked :
    rawMomentVCounts 167 = generatedVCounts167 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts167_checked :
    rawMomentQCounts 167 = generatedQCounts167 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients167_checked :
    rawMomentStateCoefficientList 167 = generatedStateCoefficients167 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts167_checked, qCounts167_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
