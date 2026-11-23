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
public import Structure.v1.Atlas.TheoryOfComputation.code.Decidability

@[expose] public section

namespace Decidability

namespace TuringMachine

variable {Γ : Type}

/-- `d.accepts` holds when the underlying TM `d.tm` accepts the input `d.input`. -/
def TMDesc.accepts (d : TMDesc Γ) : Prop :=
  @TM.accepts d.Q Γ d.decEq d.tm d.input

/-- `d.halts` holds when the underlying TM `d.tm` halts (accepts or rejects) on the input
`d.input`. -/
def TMDesc.halts (d : TMDesc Γ) : Prop :=
  @TM.halts d.Q Γ d.decEq d.tm d.input

end TuringMachine
end Decidability
