/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.BigOperators
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines
import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
import Def.v1.Atlas.TheoryOfComputation.code.SharpSAT
import Def.v1.Atlas.TheoryOfComputation.code.GeographyGame.Part2
import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part5
open Computability
open TuringMachine


namespace SpaceComplexity

/-- An encoding of Generalized Geography instances `(G, a)` (a digraph with a starting
node) as strings over alphabet `Γ`. -/
structure GGEncoding (Γ : Type) [Inhabited Γ] where
  V : Type
  decEqV : DecidableEq V
  encode : Digraph V × V → List Γ
  decode : List Γ → Option (Digraph V × V)
  encode_injective : Function.Injective encode
  decode_encode : ∀ p : Digraph V × V, decode (encode p) = some p
  blank_free : ∀ p : Digraph V × V, (default : Γ) ∉ encode p
  encode_decode : ∀ (l : List Γ) (p : Digraph V × V), decode l = some p → encode p = l
  fintypeV : Fintype V
  nonemptyV : Nonempty V

end SpaceComplexity
