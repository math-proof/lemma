/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GraphNonIsoIP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TheoryOfComputation.code.InteractiveProofs
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.Probabilistic
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

/-- A toy default implementation of `GraphPermuter` used to show that the
structure is inhabited.

It does not implement an actual graph permutation; instead it produces
length-distinguishable outputs whenever the input pair is not isomorphic
(satisfying `identify_correct`) and a single constant output whenever the
input is isomorphic (satisfying `iso_challenge_eq`). It suffices for proving
`ISO_bar ∈ IP`. -/
noncomputable def defaultGraphPermuter {Γ : Type} [Inhabited Γ]
    (enc : GraphPairEncoding Γ) : GraphPermuter Γ enc where
  challenge w b _seed :=
    if @decide (w ∈ ISO enc) (Classical.dec _) then
      w
    else
      if b then w ++ [default] else w
  iso_challenge_eq w hw seed := by
    have htrue : @decide (w ∈ ISO enc) (Classical.dec _) = true :=
      @decide_eq_true _ (Classical.dec _) hw
    simp [htrue]
  identify w msg :=
    decide (msg.length > w.length)
  identify_correct w hw b seed := by
    have hfalse : @decide (w ∈ ISO enc) (Classical.dec _) = false :=
      @decide_eq_false _ (Classical.dec _) hw
    simp only [hfalse]
    cases b <;> simp [List.length_append]

/-- The verifier in the graph non-isomorphism IP protocol.

Using two random coins, in two rounds it sends `perm.challenge w bᵢ w` for
`b₀, b₁ ∈ {true, false}` and finally accepts iff the prover's responses
correctly identify the bits, i.e. both `coins ⟨0⟩ == guess1` and
`coins ⟨1⟩ == guess2` hold. -/
def isoBarVerifier {Γ : Type} [DecidableEq Γ]
    {enc : GraphPairEncoding Γ}
    (perm : GraphPermuter Γ enc) : Verifier Bool Γ :=
  { sendMessage := fun w n coins transcript =>
      if h : n ≥ 2 then


        if transcript.length = 0 then
          perm.challenge w (coins ⟨0, by omega⟩) w
        else if transcript.length = 2 then
          perm.challenge w (coins ⟨1, by omega⟩) w
        else []
      else []
    decide := fun w n coins transcript =>
      if h : n ≥ 2 then


        match transcript with
        | [_, response1, _, response2] =>
          let guess1 : Bool := !response1.isEmpty
          let guess2 : Bool := !response2.isEmpty
          (coins ⟨0, by omega⟩ == guess1) && (coins ⟨1, by omega⟩ == guess2)
        | _ => false
      else false }

/-- The honest prover in the graph non-isomorphism IP protocol.

After each verifier challenge `c` it calls `perm.identify input c` and replies
with a nonempty marker (`[default]`) if the bit is identified as `true`, and
the empty list otherwise. By `identify_correct`, when `w ∉ ISO enc` (i.e.
`w ∈ ISO_bar enc`) the honest prover always recovers the verifier's bits and
the protocol accepts with probability 1. -/
def isoBarHonestProver {Γ : Type} [Inhabited Γ]
    {enc : GraphPairEncoding Γ}
    (perm : GraphPermuter Γ enc) : Prover Γ :=
  fun input transcript =>
    match transcript with
    | [challenge] =>

      if perm.identify input challenge then [default] else []
    | [_, _, challenge] =>

      if perm.identify input challenge then [default] else []
    | _ => []
