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
import Abbrev.v1.Atlas.BooleanFunctions.code.PCP.Part2


namespace PCP

def Literal.satisfiedBy {n : ℕ} (l : Literal n) (σ : Assignment n) : Bool :=
  σ l.var == l.polarity

def Clause.satisfiedBy {n : ℕ} (c : Clause n) (σ : Assignment n) : Bool :=
  c.lit₁.satisfiedBy σ || c.lit₂.satisfiedBy σ || c.lit₃.satisfiedBy σ

end PCP
