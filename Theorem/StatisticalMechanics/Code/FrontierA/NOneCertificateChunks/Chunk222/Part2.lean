/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk222.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk222.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts445_checked :
    rawMomentVCounts 445 = generatedVCounts445 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts445_checked :
    rawMomentQCounts 445 = generatedQCounts445 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients445_checked :
    rawMomentStateCoefficientList 445 = generatedStateCoefficients445 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts445_checked, qCounts445_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
