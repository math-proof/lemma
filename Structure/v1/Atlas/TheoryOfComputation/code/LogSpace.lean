/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LogSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.Ring
public import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
public import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
public import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
public import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
public import Def.v1.Atlas.TheoryOfComputation.code.LogSpace
public section

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
