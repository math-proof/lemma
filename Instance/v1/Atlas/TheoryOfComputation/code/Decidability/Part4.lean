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
public import Def.v1.Atlas.TheoryOfComputation.code.Decidability.Part10
@[expose] public section

namespace Decidability

namespace TuringMachine

variable {Γ : Type}

namespace LBADecidability

open TuringMachine

variable {Γ : Type}

/-- Acceptance of an LBA description is decidable (classically). Constructively this follows
from the finiteness of LBA configurations, which bounds the search for an accepting run. -/
noncomputable instance lbaDesc_accepts_decidable
    (d : LBADesc Γ) : Decidable d.accepts := Classical.dec _


end LBADecidability
end TuringMachine
end Decidability
