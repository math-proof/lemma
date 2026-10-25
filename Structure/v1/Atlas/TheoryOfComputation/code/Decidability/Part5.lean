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
import Def.v1.Atlas.TheoryOfComputation.code.Decidability.Part7


namespace Decidability

namespace TuringMachine

variable {Γ : Type}

namespace LBADecidability

open TuringMachine

/-- An `LBADesc` packages a linearly bounded automaton (a finite-state TM constrained to its
input region) with an input string. Following Sipser, `LBA = ⟨B, w⟩` is the typical input to
`A_LBA`. -/
structure LBADesc (Γ : Type) where
  Q : Type
  decEq : DecidableEq Q
  finQ : Fintype Q
  lba : @LBA Q Γ decEq
  input : List Γ

end LBADecidability
end TuringMachine
end Decidability
