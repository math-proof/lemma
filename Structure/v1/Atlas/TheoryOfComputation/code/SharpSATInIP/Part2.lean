/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SharpSATInIP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.InteractiveProofs.Part2
import Def.v1.Atlas.TheoryOfComputation.code.SharpSAT
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Def.v1.Atlas.TheoryOfComputation.code.SharpSATInIP.Part2


namespace SharpSATInIP

open InteractiveProofs NPCompleteness TuringMachine

/--
A `SumCheckEncoding` extends a `SharpSATEncoding` with the auxiliary data needed
to run the sum-check protocol:

* a finite field `ZMod q` (with `q ≠ 0`),
* a fixed number of random bits per field element (`bitsPerField`) with a
  conversion `coinsToField`,
* encode/decode functions for both a single field element and a triple of field
  elements (used by the verifier to send a challenge and by the prover to send
  the three values `v₀`, `v₁`, `v_r` per round).
-/
structure SumCheckEncoding (Γ : Type) extends SharpSATEncoding Γ where
  q : ℕ
  hq_ne : NeZero q
  bitsPerField : ℕ
  hbits_pos : 0 < bitsPerField
  coinsToField : (Fin bitsPerField → Bool) → ZMod q
  encodeTriple : ZMod q → ZMod q → ZMod q → List Γ
  decodeTriple : List Γ → Option (ZMod q × ZMod q × ZMod q)
  decode_encodeTriple : ∀ a b c, decodeTriple (encodeTriple a b c) = some (a, b, c)
  encodeField : ZMod q → List Γ
  decodeField : List Γ → Option (ZMod q)
  decode_encodeField : ∀ x, decodeField (encodeField x) = some x

end SharpSATInIP
