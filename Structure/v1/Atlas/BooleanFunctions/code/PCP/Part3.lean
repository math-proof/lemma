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
import Def.v1.Atlas.BooleanFunctions.code.PCP.Part3


namespace PCP

structure Literal (n : ℕ) where
  var : Fin n
  polarity : Bool

structure Clause (n : ℕ) where
  lit₁ : Literal n
  lit₂ : Literal n
  lit₃ : Literal n

end PCP
