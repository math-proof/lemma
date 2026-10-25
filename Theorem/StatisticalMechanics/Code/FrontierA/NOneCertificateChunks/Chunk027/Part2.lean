/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk027.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk027.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts55_checked :
    rawMomentVCounts 55 = generatedVCounts55 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts55_checked :
    rawMomentQCounts 55 = generatedQCounts55 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients55_checked :
    rawMomentStateCoefficientList 55 = generatedStateCoefficients55 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts55_checked, qCounts55_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
