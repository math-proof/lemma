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
public import Instance.v1.Atlas.TheoryOfComputation.code.Decidability

@[expose] public section

namespace Decidability

namespace TuringMachine

variable {Γ : Type}

namespace TuringMachine

variable {Γ : Type}

/-- A language is "finitely Turing-decidable" if it is decided by some TM whose state set is
`Fin n` for some `n`. Up to renaming of states this is no weaker than `IsTuringDecidable`, but
restricting to `Fin n` makes the collection of such machines countable. -/
def IsTuringDecidableFinite {Γ : Type} (A : Set (List Γ)) : Prop :=
  ∃ (n : ℕ) (M : TM (Fin n) Γ), M.isDecider ∧ M.language = A

end TuringMachine
end TuringMachine
end Decidability
