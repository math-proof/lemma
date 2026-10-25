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
import Abbrev.v1.Atlas.TheoryOfComputation.code.TuringMachines


namespace TuringMachine

open Direction

/-- A configuration of a Turing machine: current `state`, head position `headPos`
on the tape, and the full tape contents `tape`. -/
structure Config (Q : Type) (Γ : Type) where
  state : Q
  headPos : ℤ
  tape : Tape Γ

end TuringMachine
