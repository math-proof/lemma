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
import Inductive.v1.Atlas.TheoryOfComputation.code.LogSpace
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
