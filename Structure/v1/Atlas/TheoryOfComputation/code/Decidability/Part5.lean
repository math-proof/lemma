/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Countable
public import Mathlib.Computability.Language
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines
public import Notation.v1.Atlas.TheoryOfComputation.code.Reductions
public import Def.v1.Atlas.TheoryOfComputation.code.Decidability.Part7


public section

namespace Decidability

namespace TuringMachine

variable {Γ : Type}

namespace LBADecidability

open TuringMachine

/-- An `LBADesc` packages a linearly bounded automaton (a finite-state TM constrained to its
input region) with an input string. Following Sipser, `LBA = ⟨B, w⟩` is the typical input to
`A_LBA`. -/
structure LBADesc (Γ : Type) where
  Q : Type
  decEq : DecidableEq Q
  finQ : Fintype Q
  lba : @LBA Q Γ decEq
  input : List Γ

end LBADecidability
end TuringMachine
end Decidability
