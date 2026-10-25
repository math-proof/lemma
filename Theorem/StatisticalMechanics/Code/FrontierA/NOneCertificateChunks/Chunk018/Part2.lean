/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk018.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk018.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts37_checked :
    rawMomentVCounts 37 = generatedVCounts37 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts37_checked :
    rawMomentQCounts 37 = generatedQCounts37 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients37_checked :
    rawMomentStateCoefficientList 37 = generatedStateCoefficients37 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts37_checked, qCounts37_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
