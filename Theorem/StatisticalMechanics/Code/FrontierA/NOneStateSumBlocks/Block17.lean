module
public import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
public import Def.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block17


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block17.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in


theorem directStateBlock17_checked :
    rawMomentDirectBlock 34 2 =
      rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock17 := by
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
