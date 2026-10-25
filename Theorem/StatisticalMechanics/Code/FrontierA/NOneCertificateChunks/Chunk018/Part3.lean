/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk018.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk018.Part3


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem coefficientChunk18_checked :
    rawMomentCoefficientSmallList 36 2 = generatedCoefficientChunk18 := by
  unfold rawMomentCoefficientSmallList
  change addCoefficientLists
    (addCoefficientLists (List.replicate 800 0)
      (rawMomentStateCoefficientList 36))
    (rawMomentStateCoefficientList 37) = generatedCoefficientChunk18
  rw [stateCoefficients36_checked, stateCoefficients37_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
