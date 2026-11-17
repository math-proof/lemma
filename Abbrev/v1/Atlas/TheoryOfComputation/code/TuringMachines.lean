/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TuringMachines.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.RelClasses
public import Structure.v1.Atlas.TheoryOfComputation.code.TuringMachines

@[expose] public section


namespace TuringMachine

open Direction

/-- A (two-way infinite) Turing-machine tape: a function from cell index `ℤ` to
tape-alphabet symbols. -/
abbrev Tape (Γ : Type) := ℤ → Γ

end TuringMachine
