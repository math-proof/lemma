/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.BigOperators
public import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines
public import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
public import Def.v1.Atlas.TheoryOfComputation.code.SharpSAT
public import Def.v1.Atlas.TheoryOfComputation.code.GeographyGame.Part2
public import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part4
@[expose] public section

open Computability
open TuringMachine


namespace SpaceComplexity

variable {α : Type*}

/-- Decidable equality on `TQBFState Γ`, inherited from `Fin 3 × List Γ`. -/
instance (Γ : Type) [DecidableEq Γ] : DecidableEq (TQBFState Γ) :=
  inferInstanceAs (DecidableEq (Fin 3 × List Γ))

end SpaceComplexity
