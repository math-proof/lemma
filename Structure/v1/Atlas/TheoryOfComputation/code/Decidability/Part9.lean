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
import Def.v1.Atlas.TheoryOfComputation.code.Decidability.Part12


namespace Decidability

namespace TuringMachine

variable {Γ : Type}

/-- An injective encoding/decoding scheme that turns context-free grammars over `Γ` into
strings over `Γ`. Used to formulate `ALL_CFG`. -/
structure CFGEncoding (Γ : Type) where
  encode : ContextFreeGrammar Γ → List Γ
  decode : List Γ → Option (ContextFreeGrammar Γ)
  encode_injective : Function.Injective encode
  decode_encode : ∀ g, decode (encode g) = some g


end TuringMachine
end Decidability
