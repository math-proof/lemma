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
import Structure.v1.Atlas.TheoryOfComputation.code.TuringMachines


namespace TuringMachine

open Direction

/-- A (two-way infinite) Turing-machine tape: a function from cell index `ℤ` to
tape-alphabet symbols. -/
abbrev Tape (Γ : Type) := ℤ → Γ

end TuringMachine
