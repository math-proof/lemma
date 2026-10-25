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
import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines


namespace TuringMachine

open Direction

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/-- A Linearly Bounded Automaton (LBA): a 1-tape Turing machine whose head can
never move off the input portion of the tape. Formally, on every input `w` and
every step `n`, the head position lies in `[0, max 1 |w|)`. -/
structure LBA (Q : Type) (Γ : Type) [DecidableEq Q] where
  toTM : TM Q Γ
  head_bounded : ∀ (w : List Γ) (n : ℕ),
    let c := toTM.runOnInput w n
    0 ≤ c.headPos ∧ c.headPos < ↑(max 1 w.length)

end TuringMachine
