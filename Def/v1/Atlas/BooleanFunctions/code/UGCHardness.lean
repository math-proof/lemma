/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UGCHardness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.BooleanFunctions.code.UniqueGames.Part8
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.UniqueGames

@[expose] public section

namespace UGCHardness

def UGC : Prop :=
  ∀ ε δ : ℝ, ε > 0 → δ > 0 →
    ∃ k : ℕ, UniqueGames.IsNPHardGapUniqueGame k (1 - ε) δ


end UGCHardness
