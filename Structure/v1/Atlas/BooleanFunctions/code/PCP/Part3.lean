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
public import Def.v1.Atlas.BooleanFunctions.code.PCP.Part3


public section

namespace PCP

structure Literal (n : ℕ) where
  var : Fin n
  polarity : Bool

structure Clause (n : ℕ) where
  lit₁ : Literal n
  lit₂ : Literal n
  lit₃ : Literal n

end PCP
