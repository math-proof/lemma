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
import Def.v1.Atlas.TheoryOfComputation.code.LogSpace
open SpaceComplexity
open TuringMachine


namespace LogSpace

/-- A log-space Turing machine configuration `(q, p_1, p_2, t)` consisting of
the current state, the input-tape head position `p_1`, the work-tape head
position `p_2`, and the contents `t` of the work tape. -/
structure LogSpaceConfig (Q : Type) (Γ : Type) where
  state : Q
  inputHeadPos : ℕ
  workHeadPos : ℕ
  workTape : ℕ → Γ

end LogSpace
