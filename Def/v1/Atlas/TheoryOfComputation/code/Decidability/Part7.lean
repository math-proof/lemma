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
import Structure.v1.Atlas.TheoryOfComputation.code.Decidability.Part4


namespace Decidability

namespace TuringMachine

variable {Γ : Type}

namespace TuringMachine

variable {Γ : Type}

variable {Γ : Type}

/-- The Post Correspondence Problem language `PCP = {⟨P⟩ | P has a match}`. By Sipser's
Lecture 10 theorem, this language is undecidable. -/
def PCP (enc : PCPEncoding Γ) : Set (List Γ) :=
  {s | ∃ P : PCPInstance Γ, enc.encode P = s ∧ hasMatch P}

end TuringMachine
end TuringMachine
end Decidability
