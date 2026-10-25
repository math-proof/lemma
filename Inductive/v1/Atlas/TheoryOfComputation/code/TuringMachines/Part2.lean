/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TuringMachines.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Order.RelClasses
import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part3


namespace TuringMachine

open Direction

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/-- A working tape alphabet for the language `{a^k b^k}` decider: input symbols
`a` and `b`, plus a marker `cross` (used to cross off symbols during scanning)
and a `blank`. -/
inductive ABSymbol where
  | a : ABSymbol
  | b : ABSymbol
  | cross : ABSymbol
  | blank : ABSymbol
  deriving DecidableEq, Repr, Inhabited

end TuringMachine
