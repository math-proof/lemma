/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GraphNonIsoIP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.InteractiveProofs.Part2
import Def.v1.Atlas.TheoryOfComputation.code.Probabilistic.Part5
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Probabilistic
import Mathlib.Tactic


namespace GraphNonIsoIP

open InteractiveProofs Probabilistic TuringMachine

/-- The **graph non-isomorphism** language `\overline{ISO}`: the complement of
`ISO = { ⟨G, H⟩ | G and H are isomorphic graphs }` under a fixed encoding of
graph pairs. Membership `⟨G, H⟩ ∈ ISO_bar` says that the two graphs are *not*
isomorphic. -/
def ISO_bar {Γ : Type} (enc : GraphPairEncoding Γ) : Set (List Γ) :=
  (ISO enc)ᶜ

end GraphNonIsoIP
