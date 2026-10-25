/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk193.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk193.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts387_checked :
    rawMomentVCounts 387 = generatedVCounts387 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts387_checked :
    rawMomentQCounts 387 = generatedQCounts387 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients387_checked :
    rawMomentStateCoefficientList 387 = generatedStateCoefficients387 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts387_checked, qCounts387_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
