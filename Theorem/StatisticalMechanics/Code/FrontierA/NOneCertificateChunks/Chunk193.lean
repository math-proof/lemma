/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk193.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk193


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts386_checked :
    rawMomentVCounts 386 = generatedVCounts386 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts386_checked :
    rawMomentQCounts 386 = generatedQCounts386 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients386_checked :
    rawMomentStateCoefficientList 386 = generatedStateCoefficients386 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts386_checked, qCounts386_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
