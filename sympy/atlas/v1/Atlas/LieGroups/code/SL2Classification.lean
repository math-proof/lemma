/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Classification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.SL2Representations
import Lemma.Complex.IsIsomorphicGK.of.IsIsomorphicGK.IsIsomorphicGK

def IsOddInteger (s : ℂ) : Prop := ∃ k : ℤ, s = 2 * (k : ℂ) + 1

def IsEvenInteger (s : ℂ) : Prop := ∃ k : ℤ, s = 2 * (k : ℂ)

inductive SL2SimpleModule where
  | finiteDim (m : ℕ)
  | discreteSeriesMinus (m : ℕ) (hm : m ≥ 1)
  | discreteSeriesPlus (m : ℕ) (hm : m ≥ 1)
  | principalSeriesEven (s : ℂ) (hs : ¬ IsOddInteger s)
  | principalSeriesOdd (s : ℂ) (hs : ¬ IsEvenInteger s)

namespace SL2SimpleModule

def kTypes : SL2SimpleModule → Set ℤ
  | finiteDim m => { n : ℤ | n.natAbs ≤ m ∧ (n : ℤ) % 2 = (m : ℤ) % 2 }
  | discreteSeriesMinus m _ => { n : ℤ | n ≥ (m : ℤ) ∧ (n - (m : ℤ)) % 2 = 0 }
  | discreteSeriesPlus m _ => { n : ℤ | n ≤ -(m : ℤ) ∧ (n + (m : ℤ)) % 2 = 0 }
  | principalSeriesEven _ _ => { n : ℤ | n % 2 = 0 }
  | principalSeriesOdd _ _ => { n : ℤ | n % 2 = 1 ∨ n % 2 = -1 }

def casimirEigenvalue : SL2SimpleModule → ℂ
  | finiteDim m => ((m : ℂ) * ((m : ℂ) + 2)) / 4
  | discreteSeriesMinus m _ => ((m : ℂ) * ((m : ℂ) - 2)) / 4
  | discreteSeriesPlus m _ => ((m : ℂ) * ((m : ℂ) - 2)) / 4
  | principalSeriesEven s _ => (s ^ 2 - 1) / 4
  | principalSeriesOdd s _ => (s ^ 2 - 1) / 4

def IsIsomorphic : SL2SimpleModule → SL2SimpleModule → Prop
  | finiteDim m₁, finiteDim m₂ => m₁ = m₂
  | discreteSeriesMinus m₁ _, discreteSeriesMinus m₂ _ => m₁ = m₂
  | discreteSeriesPlus m₁ _, discreteSeriesPlus m₂ _ => m₁ = m₂
  | principalSeriesEven s₁ _, principalSeriesEven s₂ _ => s₁ = s₂ ∨ s₁ = -s₂
  | principalSeriesOdd s₁ _, principalSeriesOdd s₂ _ => s₁ = s₂ ∨ s₁ = -s₂
  | _, _ => False

end SL2SimpleModule
open SL2SimpleModule

def SL2SimpleModule.toIrredGK : SL2SimpleModule → SL2IrredGKModule
  | .finiteDim m => .finiteDim m
  | .discreteSeriesMinus m _ =>
    if h2 : m ≥ 2 then .discreteSeriesMinus m h2 else .limitDiscreteMinus
  | .discreteSeriesPlus m _ =>
    if h2 : m ≥ 2 then .discreteSeriesPlus m h2 else .limitDiscretePlus
  | .principalSeriesEven s _ => .principalSeries s 0
  | .principalSeriesOdd s _ => .principalSeries s 1
