/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LadderNSPACE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
import Instance.v1.Atlas.TheoryOfComputation.code.LadderNSPACE
open Computability TuringMachine SpaceComplexity


namespace SpaceComplexity

/-- Encoding of a pair of strings `(u, v)` on the tape as `u ++ [separator] ++ v`,
where each symbol of `u` and `v` is lifted via `ofAlpha`. -/
def encodePair {α : Type} (u v : List α) : List (LadderTapeSymbol α) :=
  u.map LadderTapeSymbol.ofAlpha ++ [LadderTapeSymbol.separator] ++
  v.map LadderTapeSymbol.ofAlpha

/-- The on-tape language version of `LADDER_DFA`: tape words `w` that encode some pair `(u, v)`
of strings such that there is a ladder `y₁, …, y_k ∈ L(B)` of common-length strings (consecutive
ones differing in a single symbol) with `y₁ = u` and `y_k = v`. -/
def LADDER_DFA_Lang {α : Type} {σ : Type} [Fintype σ] [Fintype α]
    (B : DFA α σ) : Set (List (LadderTapeSymbol α)) :=
  {w | ∃ (u v : List α), w = encodePair u v ∧ LADDER_DFA B u v}

end SpaceComplexity
