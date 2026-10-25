/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk038.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk038.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts77_checked :
    rawMomentVCounts 77 = generatedVCounts77 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts77_checked :
    rawMomentQCounts 77 = generatedQCounts77 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients77_checked :
    rawMomentStateCoefficientList 77 = generatedStateCoefficients77 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts77_checked, qCounts77_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
