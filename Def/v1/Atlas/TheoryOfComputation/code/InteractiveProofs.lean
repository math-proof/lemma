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


namespace InteractiveProofs

open TuringMachine

/-- A *prover* `P` in an interactive proof system. Given the input `w : List Γ`
and the transcript-so-far (a list of messages already exchanged), `P` returns
the next message to send to the verifier. Provers are not restricted in
computational power. -/
def Prover (Γ : Type) : Type :=
  List Γ → List (List Γ) → List Γ

end InteractiveProofs
