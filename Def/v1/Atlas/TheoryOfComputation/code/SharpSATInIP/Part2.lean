/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SharpSATInIP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.TheoryOfComputation.code.InteractiveProofs.Part2
public import Def.v1.Atlas.TheoryOfComputation.code.SharpSAT
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring
public import Structure.v1.Atlas.TheoryOfComputation.code.SharpSATInIP

@[expose] public section

namespace SharpSATInIP

open InteractiveProofs NPCompleteness TuringMachine

/--
The language `#SAT` realised over the alphabet `Γ` via `enc`:
`{w | enc(w) = ⟨φ, k⟩ and k = #sat(φ)}`, i.e. encodings of `⟨φ, k⟩` where `φ`
has exactly `k` satisfying assignments.
-/
def SharpSAT_enc {Γ : Type} (enc : SharpSATEncoding Γ) : Set (List Γ) :=
  {w | ∃ φ k, enc.decode w = some (φ, k) ∧ k = φ.sharpSat}

end SharpSATInIP
