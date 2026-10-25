/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk107.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk107.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts215_checked :
    rawMomentVCounts 215 = generatedVCounts215 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts215_checked :
    rawMomentQCounts 215 = generatedQCounts215 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients215_checked :
    rawMomentStateCoefficientList 215 = generatedStateCoefficients215 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts215_checked, qCounts215_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
