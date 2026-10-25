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
import Structure.v1.Atlas.TheoryOfComputation.code.Decidability.Part7


namespace Decidability

namespace TuringMachine

variable {Γ : Type}

namespace ELBA

open TuringMachine

variable {Γ : Type}

/-- The language accepted by an LBA description. -/
def LBAMachineDesc.language (d : LBAMachineDesc Γ) : Set (List Γ) :=
  @LBA.language d.Q Γ d.decEq d.lba

end ELBA
end TuringMachine
end Decidability
