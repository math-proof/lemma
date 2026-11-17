/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.BigOperators
public import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
public import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines
public import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
public import Def.v1.Atlas.TheoryOfComputation.code.SharpSAT
public import Def.v1.Atlas.TheoryOfComputation.code.GeographyGame.Part2
public import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part3
public section

open Computability
open TuringMachine


namespace SpaceComplexity

variable {α : Type*}

/-- **Corollary of Savitch's Theorem**: `NPSPACE = PSPACE`. Polynomial nondeterministic
space coincides with polynomial deterministic space. -/
structure QBFEncoding (Γ : Type) [Inhabited Γ] where
  encode : QBF → List Γ
  decode : List Γ → Option QBF
  encode_injective : Function.Injective encode
  decode_encode : ∀ ψ : QBF, decode (encode ψ) = some ψ
  blank_free : ∀ ψ : QBF, (default : Γ) ∉ encode ψ
  encode_decode : ∀ (l : List Γ) (ψ : QBF), decode l = some ψ → encode ψ = l

end SpaceComplexity
