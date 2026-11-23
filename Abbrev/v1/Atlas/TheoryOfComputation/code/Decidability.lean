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
public import Def.v1.Atlas.TheoryOfComputation.code.Decidability.Part4

@[expose] public section


namespace Decidability

namespace TuringMachine

variable {Γ : Type}

namespace TuringMachine

variable {Γ : Type}

/-- The raw data of a finite-state Turing machine over `Γ`: a state count `n`, a blank symbol,
a transition function, and start/accept/reject states. This is the carrier used to enumerate
TMs in a countable family. -/
abbrev TMDescType (Γ : Type) :=
  Σ n : ℕ, Γ × (Fin n → Γ → Fin n × Γ × Direction) × Fin n × Fin n × Fin n

end TuringMachine
end TuringMachine
end Decidability
