/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/HamiltonTournaments.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
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
