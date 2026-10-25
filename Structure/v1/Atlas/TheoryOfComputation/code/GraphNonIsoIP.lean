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
import Def.v1.Atlas.TheoryOfComputation.code.GraphNonIsoIP


namespace GraphNonIsoIP

open InteractiveProofs Probabilistic TuringMachine

/-- A `GraphPermuter` packages the random-permutation oracle used by the
honest prover in the IP protocol for graph non-isomorphism.

* `challenge w b seed` returns the verifier's challenge graph obtained by
  randomly permuting either graph (`b = false`) or the other (`b = true`).
* `iso_challenge_eq` says that **if the input pair `w` is isomorphic** then
  the two challenge distributions coincide: the prover cannot distinguish.
* `identify msg` reads a challenge back and reports which of the two graphs
  it came from.
* `identify_correct` says that **if the input pair `w` is not isomorphic** then
  `identify` recovers the bit `b` that the verifier used. -/
structure GraphPermuter (Γ : Type) (enc : GraphPairEncoding Γ) where
  challenge : List Γ → Bool → List Γ → List Γ
  iso_challenge_eq : ∀ w : List Γ, w ∈ ISO enc →
    ∀ (seed : List Γ), challenge w true seed = challenge w false seed
  identify : List Γ → List Γ → Bool
  identify_correct : ∀ w : List Γ, w ∉ ISO enc →
    ∀ (b : Bool) (seed : List Γ), identify w (challenge w b seed) = b

end GraphNonIsoIP
