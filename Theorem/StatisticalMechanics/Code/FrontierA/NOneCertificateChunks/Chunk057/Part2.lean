/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk057.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk057.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts115_checked :
    rawMomentVCounts 115 = generatedVCounts115 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts115_checked :
    rawMomentQCounts 115 = generatedQCounts115 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients115_checked :
    rawMomentStateCoefficientList 115 = generatedStateCoefficients115 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts115_checked, qCounts115_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
