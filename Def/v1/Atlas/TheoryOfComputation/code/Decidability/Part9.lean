/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Countable
import Mathlib.Computability.Language
import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines
import Notation.v1.Atlas.TheoryOfComputation.code.Reductions
import Structure.v1.Atlas.TheoryOfComputation.code.Decidability.Part6


namespace Decidability

namespace TuringMachine

variable {Γ : Type}

namespace LBADecidability

open TuringMachine

variable {Γ : Type}

/-- The acceptance language for LBAs: `A_LBA = {⟨B, w⟩ | LBA B accepts w}`. Sipser's Lecture 10
theorem shows this language is *decidable*. -/
def A_LBA (enc : LBAEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : LBADesc Γ, enc.encode d = s ∧ d.accepts}

/-- A *bounded configuration* records only the data of an LBA configuration that can vary in
the bounded simulation: state, head position in `Fin m`, and tape contents on the first `m`
cells. The total number of such configurations is finite. -/
def BoundedConfig (Q : Type) (Γ : Type) (m : ℕ) :=
  Q × Fin m × (Fin m → Γ)

end LBADecidability
end TuringMachine
end Decidability
