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
import Instance.v1.Atlas.TheoryOfComputation.code.Decidability


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
