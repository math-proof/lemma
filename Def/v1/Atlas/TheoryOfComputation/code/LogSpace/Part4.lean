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
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
public import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
public import Inductive.v1.Atlas.TheoryOfComputation.code.LogSpace

@[expose] public section

open SpaceComplexity
open TuringMachine


namespace LogSpace

/-- The set of vertices reachable from `s` in `G` within at most `d` steps. -/
def reachableSet {V : Type*} (G : V → V → Prop) (d : ℕ) (s : V) : Set V :=
  {u | BoundedReachable G d s u}

/-- The count `c_d = |reachableSet G d s|` of vertices reachable from `s`
within `d` steps. In the Immerman–Szelepcsényi proof this is the quantity
computed inductively by an NL machine. -/
noncomputable def reachableCount {V : Type*} (G : V → V → Prop) (d : ℕ) (s : V) : ℕ :=
  Set.ncard (reachableSet G d s)

end LogSpace
