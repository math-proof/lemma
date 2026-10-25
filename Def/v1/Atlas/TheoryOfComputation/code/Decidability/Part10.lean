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
import Instance.v1.Atlas.TheoryOfComputation.code.Decidability.Part3


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
