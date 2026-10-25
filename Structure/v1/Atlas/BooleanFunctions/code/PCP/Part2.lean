/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/PCP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Def.v1.Atlas.BooleanFunctions.code.PCP.Part2


namespace PCP

structure PCPVerifier (n : ℕ) where
  numRandom : ℕ
  numQueries : ℕ
  proofLen : ℕ
  queryPositions : BinaryString numRandom → Fin numQueries → Fin proofLen
  decide : BinaryString n → BinaryString numRandom → BinaryString numQueries → Bool

end PCP
