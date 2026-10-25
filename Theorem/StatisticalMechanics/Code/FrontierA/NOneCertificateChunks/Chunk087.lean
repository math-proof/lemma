/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk087.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk087


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts174_checked :
    rawMomentVCounts 174 = generatedVCounts174 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts174_checked :
    rawMomentQCounts 174 = generatedQCounts174 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients174_checked :
    rawMomentStateCoefficientList 174 = generatedStateCoefficients174 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts174_checked, qCounts174_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
