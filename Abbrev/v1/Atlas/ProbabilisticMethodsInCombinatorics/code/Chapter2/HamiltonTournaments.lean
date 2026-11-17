/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/HamiltonTournaments.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fin.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
@[expose] public section

set_option maxHeartbeats 800000

open Finset Fintype


namespace SzeleTournament

/-- The set of unordered edge positions on $n$ labeled vertices, encoded as ordered
pairs $(i, j)$ with $i < j$. -/
abbrev EdgeSet (n : ℕ) := { p : Fin n × Fin n // p.1 < p.2 }

/-- A tournament on $n$ vertices: an orientation assigning a Boolean direction to each
unordered edge in `EdgeSet n`. -/
abbrev Tournament (n : ℕ) := EdgeSet n → Bool

end SzeleTournament
