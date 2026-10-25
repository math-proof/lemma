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
import Def.v1.Atlas.TheoryOfComputation.code.Decidability.Part11


namespace Decidability

namespace TuringMachine

variable {Γ : Type}

namespace ELBA

open TuringMachine

variable {Γ : Type}

/-- Injective encoding/decoding of LBA machine descriptions, used to formulate `E_LBA`. -/
structure LBAMachineEncoding (Γ : Type) where
  encode : LBAMachineDesc Γ → List Γ
  decode : List Γ → Option (LBAMachineDesc Γ)
  encode_injective : Function.Injective encode
  decode_encode : ∀ d, decode (encode d) = some d

end ELBA
end TuringMachine
end Decidability
