/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk200.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk200.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts401_checked :
    rawMomentVCounts 401 = generatedVCounts401 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts401_checked :
    rawMomentQCounts 401 = generatedQCounts401 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients401_checked :
    rawMomentStateCoefficientList 401 = generatedStateCoefficients401 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts401_checked, qCounts401_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
