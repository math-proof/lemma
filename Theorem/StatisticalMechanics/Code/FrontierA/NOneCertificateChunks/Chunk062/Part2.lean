/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk062.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk062.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts125_checked :
    rawMomentVCounts 125 = generatedVCounts125 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts125_checked :
    rawMomentQCounts 125 = generatedQCounts125 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients125_checked :
    rawMomentStateCoefficientList 125 = generatedStateCoefficients125 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts125_checked, qCounts125_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
