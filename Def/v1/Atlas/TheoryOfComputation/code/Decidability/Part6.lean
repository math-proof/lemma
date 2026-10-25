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
import Structure.v1.Atlas.TheoryOfComputation.code.Decidability.Part3


namespace Decidability

namespace TuringMachine

variable {Γ : Type}

namespace TuringMachine

variable {Γ : Type}

/-- A *PCP instance* is a finite list of dominoes. -/
def PCPInstance (α : Type) := List (Domino α)

/-- A PCP instance `P` *has a match* if there is a nonempty sequence of indices `i₁, …, iₖ` such
that concatenating the tops in order produces the same string as concatenating the bottoms in
order. The PCP language is precisely the set of encoded instances with a match. -/
def hasMatch {α : Type} (P : PCPInstance α) : Prop :=
  ∃ (indices : List (Fin P.length)),
    indices ≠ [] ∧
    (indices.map (fun i => (P.get i).top)).flatten =
    (indices.map (fun i => (P.get i).bottom)).flatten

end TuringMachine
end TuringMachine
end Decidability
