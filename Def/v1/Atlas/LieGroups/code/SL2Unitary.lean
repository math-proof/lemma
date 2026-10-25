/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Unitary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.SL2Representations.Part2
import Lemma.Complex.IsIsomorphicGK.of.IsIsomorphicGK.IsIsomorphicGK
set_option maxHeartbeats 800000


noncomputable section

open Complex

namespace SL2IrredGKModule

def principalSeriesParamSq : SL2IrredGKModule → ℂ
  | finiteDim n => ((n + 1 : ℕ) : ℂ) ^ 2
  | principalSeries ν _ => ν ^ 2
  | discreteSeriesPlus n _ => ((n : ℂ) - 1) ^ 2
  | discreteSeriesMinus n _ => ((n : ℂ) - 1) ^ 2
  | limitDiscretePlus => 0
  | limitDiscreteMinus => 0

def IsBargmannUnitary (μ : SL2IrredGKModule) : Prop :=
  (μ.principalSeriesParamSq.im = 0) ∧
  (∀ n ∈ μ.kTypes, (n + 2 : ℤ) ∈ μ.kTypes →
    μ.principalSeriesParamSq.re < ((n + 1 : ℤ) : ℝ) ^ 2)

end SL2IrredGKModule
end
