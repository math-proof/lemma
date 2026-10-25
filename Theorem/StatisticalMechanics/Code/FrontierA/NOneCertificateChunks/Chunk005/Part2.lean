/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk005.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk005.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts11_checked :
    rawMomentVCounts 11 = generatedVCounts11 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts11_checked :
    rawMomentQCounts 11 = generatedQCounts11 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients11_checked :
    rawMomentStateCoefficientList 11 = generatedStateCoefficients11 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts11_checked, qCounts11_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
