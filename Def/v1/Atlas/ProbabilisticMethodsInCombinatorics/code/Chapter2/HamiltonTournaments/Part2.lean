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
import Instance.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter2.HamiltonTournaments
set_option maxHeartbeats 800000

open Finset Fintype


namespace SzeleTournament

/-- The number of Hamilton paths in a tournament $T$, defined as the cardinality of the
set of permutations $\sigma$ for which `IsHamiltonPath T σ` holds. -/
noncomputable def numHamiltonPaths {n : ℕ} (T : Tournament n) : ℕ :=
  (Finset.univ.filter (IsHamiltonPath T)).card

end SzeleTournament
