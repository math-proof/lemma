/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Complexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines
import Def.v1.Atlas.TheoryOfComputation.code.NondeterministicTM
import Notation.v1.Atlas.TheoryOfComputation.code.Reductions
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Def.v1.Atlas.TheoryOfComputation.code.Complexity


namespace TuringMachine

open TuringMachine

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/-- Notation `A ≤ₚ B` for polynomial-time mapping reducibility. -/
scoped infixl:50 " ≤ₚ " => PolyReducible

end TuringMachine
