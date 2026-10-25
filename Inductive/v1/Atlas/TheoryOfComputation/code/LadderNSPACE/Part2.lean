/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LadderNSPACE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
import Def.v1.Atlas.TheoryOfComputation.code.LadderNSPACE
open Computability TuringMachine SpaceComplexity


namespace SpaceComplexity

/-- The phases of the linear-space NTM that decides `LADDER_DFA`.
- `readInput`: reading and buffering the input pair `⟨u, v⟩` from the tape.
- `searchFwd`: nondeterministically guessing the next rung of the ladder.
- `searchBack`: moving the head back to the working area between rungs.
- `accepted` / `rejected`: terminal states. -/
inductive LadderPhase
  | readInput | searchFwd | searchBack | accepted | rejected
  deriving DecidableEq, Fintype

end SpaceComplexity
