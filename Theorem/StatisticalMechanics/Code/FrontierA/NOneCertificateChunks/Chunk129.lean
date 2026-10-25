/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk129.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk129


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts258_checked :
    rawMomentVCounts 258 = generatedVCounts258 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts258_checked :
    rawMomentQCounts 258 = generatedQCounts258 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients258_checked :
    rawMomentStateCoefficientList 258 = generatedStateCoefficients258 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts258_checked, qCounts258_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
