/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Unitary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.SL2Representations.Part2
import Lemma.Complex.IsIsomorphicGK.of.IsIsomorphicGK.IsIsomorphicGK
import Inductive.v1.Atlas.LieGroups.code.SL2Unitary
set_option maxHeartbeats 800000


noncomputable section

open Complex

namespace SL2UnitaryIrred

def toIrredGKModule : SL2UnitaryIrred → SL2IrredGKModule
  | .discreteSeriesPlus m _ =>
      if h : m ≥ 2 then SL2IrredGKModule.discreteSeriesPlus m h
      else SL2IrredGKModule.limitDiscretePlus
  | .discreteSeriesMinus m _ =>
      if h : m ≥ 2 then SL2IrredGKModule.discreteSeriesMinus m h
      else SL2IrredGKModule.limitDiscreteMinus
  | .unitaryPrincipalSeries t ε _ =>
      SL2IrredGKModule.principalSeries ((↑t : ℂ) * I) ε
  | .complementarySeries s _ _ =>
      SL2IrredGKModule.principalSeries (↑s : ℂ) (0 : ZMod 2)
  | .trivial => SL2IrredGKModule.finiteDim 0

end SL2UnitaryIrred
end
