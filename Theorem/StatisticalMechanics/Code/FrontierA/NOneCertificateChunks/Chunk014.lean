/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk014.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk014


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts28_checked :
    rawMomentVCounts 28 = generatedVCounts28 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts28_checked :
    rawMomentQCounts 28 = generatedQCounts28 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients28_checked :
    rawMomentStateCoefficientList 28 = generatedStateCoefficients28 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts28_checked, qCounts28_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
