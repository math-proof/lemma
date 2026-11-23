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
public import Instance.v1.Atlas.TheoryOfComputation.code.Decidability.Part3

@[expose] public section

namespace Decidability

namespace TuringMachine

variable {Γ : Type}

namespace LBADecidability

open TuringMachine

variable {Γ : Type}

/-- Extract the bounded-configuration view of a TM configuration whose head lies in `[0, m)`. -/
def extractBoundedConfig {Q Γ : Type} (m : ℕ) (c : Config Q Γ)
    (h0 : 0 ≤ c.headPos) (h1 : c.headPos < ↑m) : BoundedConfig Q Γ m :=
  (c.state,
   ⟨c.headPos.toNat, by omega⟩,
   fun i => c.tape ↑i)

end LBADecidability
end TuringMachine
end Decidability
