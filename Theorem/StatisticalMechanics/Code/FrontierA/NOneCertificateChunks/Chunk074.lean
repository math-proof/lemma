/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk074.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk074


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts148_checked :
    rawMomentVCounts 148 = generatedVCounts148 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts148_checked :
    rawMomentQCounts 148 = generatedQCounts148 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients148_checked :
    rawMomentStateCoefficientList 148 = generatedStateCoefficients148 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts148_checked, qCounts148_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
