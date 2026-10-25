/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk175.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk175


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts350_checked :
    rawMomentVCounts 350 = generatedVCounts350 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts350_checked :
    rawMomentQCounts 350 = generatedQCounts350 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients350_checked :
    rawMomentStateCoefficientList 350 = generatedStateCoefficients350 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts350_checked, qCounts350_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
