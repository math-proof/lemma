/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LogSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Ring
import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
open SpaceComplexity
open TuringMachine


namespace LogSpace

/-- Base-2 logarithm on `ℕ`, used as the canonical space bound for the class `L = SPACE(log n)`. -/
def log : ℕ → ℕ := Nat.log 2

end LogSpace
