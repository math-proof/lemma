/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk042.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk042.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts85_checked :
    rawMomentVCounts 85 = generatedVCounts85 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts85_checked :
    rawMomentQCounts 85 = generatedQCounts85 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients85_checked :
    rawMomentStateCoefficientList 85 = generatedStateCoefficients85 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts85_checked, qCounts85_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
