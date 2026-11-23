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
public import Instance.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter2.HamiltonTournaments

@[expose] public section

set_option maxHeartbeats 800000

open Finset Fintype


namespace SzeleTournament

/-- The number of Hamilton paths in a tournament $T$, defined as the cardinality of the
set of permutations $\sigma$ for which `IsHamiltonPath T σ` holds. -/
noncomputable def numHamiltonPaths {n : ℕ} (T : Tournament n) : ℕ :=
  (Finset.univ.filter (IsHamiltonPath T)).card

end SzeleTournament
