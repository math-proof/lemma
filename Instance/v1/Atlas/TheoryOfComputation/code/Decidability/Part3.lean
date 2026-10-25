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
import Def.v1.Atlas.TheoryOfComputation.code.Decidability.Part9


namespace Decidability

namespace TuringMachine

variable {Γ : Type}

namespace LBADecidability

open TuringMachine

variable {Γ : Type}

/-- The set of bounded configurations of an LBA with state set `Q`, tape alphabet `Γ`, and
input bound `m` is finite when `Q` and `Γ` are. This finiteness is the basis of the decidability
of `A_LBA`: an LBA either accepts within `|Q| · m · |Γ|^m` steps or loops. -/
noncomputable instance instFintypeBoundedConfig (Q : Type) (Γ : Type) (m : ℕ)
    [Fintype Q] [DecidableEq Γ] [Fintype Γ] : Fintype (BoundedConfig Q Γ m) := by
  change Fintype (Q × Fin m × (Fin m → Γ))
  infer_instance

end LBADecidability
end TuringMachine
end Decidability
