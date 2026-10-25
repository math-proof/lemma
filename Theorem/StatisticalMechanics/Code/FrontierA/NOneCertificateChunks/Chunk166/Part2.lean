/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk166.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk166.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts333_checked :
    rawMomentVCounts 333 = generatedVCounts333 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts333_checked :
    rawMomentQCounts 333 = generatedQCounts333 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients333_checked :
    rawMomentStateCoefficientList 333 = generatedStateCoefficients333 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts333_checked, qCounts333_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
