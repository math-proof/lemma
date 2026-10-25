/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Classification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.SL2Representations.Part2
import Lemma.Complex.IsIsomorphicGK.of.IsIsomorphicGK.IsIsomorphicGK


def IsOddInteger (s : ℂ) : Prop := ∃ k : ℤ, s = 2 * (k : ℂ) + 1

def IsEvenInteger (s : ℂ) : Prop := ∃ k : ℤ, s = 2 * (k : ℂ)

