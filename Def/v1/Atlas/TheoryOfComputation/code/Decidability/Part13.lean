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
import Structure.v1.Atlas.TheoryOfComputation.code.Decidability.Part9


namespace Decidability

namespace TuringMachine

variable {Γ : Type}

variable {Γ : Type}

/-- The universality problem for CFGs: `ALL_CFG = {⟨G⟩ | G is a CFG and L(G) = Σ*}`. By
Sipser's Lecture 10 theorem, this language is undecidable. -/
def ALL_CFG (enc : CFGEncoding Γ) : Set (List Γ) :=
  {s | ∃ g : ContextFreeGrammar Γ, enc.encode g = s ∧ g.language = Set.univ}

end TuringMachine
end Decidability
