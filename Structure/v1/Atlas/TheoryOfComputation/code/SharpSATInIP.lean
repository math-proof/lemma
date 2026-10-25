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
import Def.v1.Atlas.TheoryOfComputation.code.SharpSATInIP


namespace SharpSATInIP

open InteractiveProofs NPCompleteness TuringMachine

/--
An encoding of `#SAT` instances `⟨φ, k⟩` (a Boolean formula together with a count)
as strings over the tape alphabet `Γ`. The roundtripping laws `decode_encode`
and `encode_decode` make the encoding a bijection onto its image.
-/
structure SharpSATEncoding (Γ : Type) where
  encode : BoolFormula × ℕ → List Γ
  decode : List Γ → Option (BoolFormula × ℕ)
  decode_encode : ∀ p, decode (encode p) = some p
  encode_decode : ∀ w p, decode w = some p → encode p = w

end SharpSATInIP
