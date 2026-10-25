/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegularIsCFL.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.CFLInterRegular
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.CFLInterRegular
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.RegularLanguages
import Def.v1.Atlas.TheoryOfComputation.code.RegularLanguages
universe u


namespace RegularIsCFL

open Computability

/-- Convert a DFA `D` to a PDA over the same input alphabet that ignores its
stack (using a trivial stack alphabet `PUnit`). The PDA's transition mirrors
`D.step` on real input symbols and has no ε-transitions or stack moves. -/
def dfaToPDA {α : Type u} {σ : Type*} (D : DFA α σ) : PDA α σ PUnit where
  step := fun q a pop =>
    match a, pop with
    | some a, none => {(D.step q a, none)}
    | _, _ => ∅
  start := D.start
  accept := D.accept

end RegularIsCFL
