/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LadderNSPACE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
import Inductive.v1.Atlas.TheoryOfComputation.code.LadderNSPACE.Part2
open Computability TuringMachine SpaceComplexity


namespace SpaceComplexity

/-- Internal control state of the `LADDER_DFA` NTM.
- `phase` is the current phase.
- `buf` is the buffered tape input being parsed in `readInput`.
- `y` is the current rung of the ladder (a string in `L(B)` of the common length).
- `v` is the target endpoint of the ladder.
- `counter` bounds the number of remaining rungs to try (so the machine halts).

Note: the components `buf`, `y`, `v` are stored inside the state for convenience but represent
information that fits in `O(n)` tape cells in the simulating linear-space NTM. -/
structure LadderState (α : Type) where
  phase : LadderPhase
  buf : List (LadderTapeSymbol α)
  y : List α
  v : List α
  counter : ℕ
  deriving DecidableEq

end SpaceComplexity
