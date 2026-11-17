/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Countable
public import Mathlib.Computability.Language
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines
public import Notation.v1.Atlas.TheoryOfComputation.code.Reductions
public import Def.v1.Atlas.TheoryOfComputation.code.Decidability.Part12


public section

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
