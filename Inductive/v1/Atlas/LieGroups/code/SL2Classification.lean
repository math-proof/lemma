/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Classification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.LieGroups.code.SL2Representations.Part2
public import Def.v1.Atlas.LieGroups.code.SL2Classification

public inductive SL2SimpleModule where
  | finiteDim (m : ℕ)
  | discreteSeriesMinus (m : ℕ) (hm : m ≥ 1)
  | discreteSeriesPlus (m : ℕ) (hm : m ≥ 1)
  | principalSeriesEven (s : ℂ) (hs : ¬ IsOddInteger s)
  | principalSeriesOdd (s : ℂ) (hs : ¬ IsEvenInteger s)

