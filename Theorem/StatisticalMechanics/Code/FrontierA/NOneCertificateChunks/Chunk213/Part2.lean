/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk213.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk213.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts427_checked :
    rawMomentVCounts 427 = generatedVCounts427 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts427_checked :
    rawMomentQCounts 427 = generatedQCounts427 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients427_checked :
    rawMomentStateCoefficientList 427 = generatedStateCoefficients427 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts427_checked, qCounts427_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
