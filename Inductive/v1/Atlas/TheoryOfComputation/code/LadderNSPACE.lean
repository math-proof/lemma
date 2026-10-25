/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LadderNSPACE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
open Computability TuringMachine SpaceComplexity


namespace SpaceComplexity

/-- Tape alphabet used by the linear-space NTM deciding `LADDER_DFA`.
It consists of the input symbols of the DFA (`ofAlpha`), a `separator` used to encode the
pair `⟨u, v⟩`, and a `blank` symbol. -/
inductive LadderTapeSymbol (α : Type) : Type
  | ofAlpha : α → LadderTapeSymbol α
  | separator : LadderTapeSymbol α
  | blank : LadderTapeSymbol α
  deriving DecidableEq

end SpaceComplexity
