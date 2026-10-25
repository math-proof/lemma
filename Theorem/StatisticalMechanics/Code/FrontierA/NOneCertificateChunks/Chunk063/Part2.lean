/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk063.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk063.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts127_checked :
    rawMomentVCounts 127 = generatedVCounts127 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts127_checked :
    rawMomentQCounts 127 = generatedQCounts127 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients127_checked :
    rawMomentStateCoefficientList 127 = generatedStateCoefficients127 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts127_checked, qCounts127_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
