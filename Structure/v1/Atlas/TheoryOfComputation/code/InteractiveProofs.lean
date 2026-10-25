/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/InteractiveProofs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.BPP.Part3
import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
import Def.v1.Atlas.TheoryOfComputation.code.InteractiveProofs


namespace InteractiveProofs

open TuringMachine

/-- A *verifier* `V` in an interactive proof system. It is parameterised by a
state-type `Q` and the alphabet `Γ`. On input `w` with `n` random coins
`Fin n → Bool`, it can `sendMessage` to the prover or `decide` (accept/reject)
based on the transcript of the conversation. -/
structure Verifier (Q : Type) (Γ : Type) where
  sendMessage : (w : List Γ) → (n : ℕ) → (Fin n → Bool) → (transcript : List (List Γ)) → List Γ
  decide : (w : List Γ) → (n : ℕ) → (Fin n → Bool) → (transcript : List (List Γ)) → Bool

end InteractiveProofs
