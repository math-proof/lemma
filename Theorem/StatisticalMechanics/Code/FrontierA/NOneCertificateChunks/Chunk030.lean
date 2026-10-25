/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk030.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk030


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts60_checked :
    rawMomentVCounts 60 = generatedVCounts60 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts60_checked :
    rawMomentQCounts 60 = generatedQCounts60 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients60_checked :
    rawMomentStateCoefficientList 60 = generatedStateCoefficients60 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts60_checked, qCounts60_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
