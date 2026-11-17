/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Complexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
public import Def.v1.Atlas.TheoryOfComputation.code.NondeterministicTM
public import Notation.v1.Atlas.TheoryOfComputation.code.Reductions
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Def.v1.Atlas.TheoryOfComputation.code.Complexity

public section


namespace TuringMachine

open TuringMachine

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/-- Notation `A ≤ₚ B` for polynomial-time mapping reducibility. -/
scoped infixl:50 " ≤ₚ " => PolyReducible

end TuringMachine
