/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk015.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk015


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts30_checked :
    rawMomentVCounts 30 = generatedVCounts30 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts30_checked :
    rawMomentQCounts 30 = generatedQCounts30 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients30_checked :
    rawMomentStateCoefficientList 30 = generatedStateCoefficients30 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts30_checked, qCounts30_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
