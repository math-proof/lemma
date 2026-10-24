/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Unitary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.SL2Representations
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

inductive SL2UnitaryIrred where
  | discreteSeriesPlus (m : ℕ) (hm : m ≥ 1)
  | discreteSeriesMinus (m : ℕ) (hm : m ≥ 1)
  | unitaryPrincipalSeries (t : ℝ) (ε : ZMod 2) (hirred : t ≠ 0 ∨ ε = 0)
  | complementarySeries (s : ℝ) (hs_ne : s ≠ 0) (hs_sq : s ^ 2 < 1)
  | trivial

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
