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
import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part2


namespace TuringMachine

open Direction

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/-- A Turing enumerator: a deterministic TM together with a "printing"
predicate `prints` specifying which strings have been output by step `n`
(viewing each `Config` as the state of the enumerator after some number of
steps). The enumerated language is the union of these print sets. -/
structure TuringEnumerator (Q : Type) (Γ : Type) [DecidableEq Q] where
  toTM : TM Q Γ
  prints : Config Q Γ → Set (List Γ)

end TuringMachine
