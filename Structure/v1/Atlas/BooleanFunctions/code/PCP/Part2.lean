/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/PCP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Nat.Log
public import Def.v1.Atlas.BooleanFunctions.code.PCP.Part2


public section

namespace PCP

structure PCPVerifier (n : ℕ) where
  numRandom : ℕ
  numQueries : ℕ
  proofLen : ℕ
  queryPositions : BinaryString numRandom → Fin numQueries → Fin proofLen
  decide : BinaryString n → BinaryString numRandom → BinaryString numQueries → Bool

end PCP
