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
public import Structure.v1.Atlas.TheoryOfComputation.code.Decidability.Part8

@[expose] public section

namespace Decidability

namespace TuringMachine

variable {Γ : Type}

namespace ELBA

open TuringMachine

variable {Γ : Type}

/-- The emptiness problem for LBAs: `E_LBA = {⟨B⟩ | L(B) = ∅}`. By Sipser's Lecture 10 theorem,
this language is undecidable. -/
def E_LBA (enc : LBAMachineEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : LBAMachineDesc Γ, enc.encode d = s ∧ d.language = ∅}

end ELBA
end TuringMachine
end Decidability
