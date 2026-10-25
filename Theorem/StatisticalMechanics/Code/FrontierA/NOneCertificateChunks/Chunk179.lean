/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk179.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk179


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts358_checked :
    rawMomentVCounts 358 = generatedVCounts358 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts358_checked :
    rawMomentQCounts 358 = generatedQCounts358 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients358_checked :
    rawMomentStateCoefficientList 358 = generatedStateCoefficients358 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts358_checked, qCounts358_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
