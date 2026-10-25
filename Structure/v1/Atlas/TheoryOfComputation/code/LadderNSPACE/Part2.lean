/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LadderNSPACE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
import Def.v1.Atlas.TheoryOfComputation.code.LadderNSPACE.Part2
open Computability TuringMachine SpaceComplexity


namespace SpaceComplexity

/-- Correctness of the NTM: `ladderNTM B` accepts exactly the encoded ladder pairs of `B`. -/
structure DFAEncoding where
  Γ : Type
  encode : {α : Type} → {σ : Type} → [Fintype α] → [Fintype σ] →
    (B : DFA α σ) → (u v : List α) → List Γ
  isValidEncoding : List Γ → Prop
  isValidEncoding_iff : ∀ w : List Γ, isValidEncoding w ↔
    ∃ (α : Type) (σ : Type) (_ : Fintype α) (_ : Fintype σ),
      ∃ (B : DFA α σ) (u v : List α), w = encode B u v
  encode_length_lower_bound : {α : Type} → {σ : Type} → [Fintype α] → [Fintype σ] →
    (B : DFA α σ) → (u v : List α) →
    u.length + v.length ≤ (encode B u v).length

end SpaceComplexity
