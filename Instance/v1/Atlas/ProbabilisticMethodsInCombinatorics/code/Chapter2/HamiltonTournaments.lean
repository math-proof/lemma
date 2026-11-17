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
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter2.HamiltonTournaments

@[expose] public section

set_option maxHeartbeats 800000

open Finset Fintype


namespace SzeleTournament

/-- Decidability instance for `IsHamiltonPath`, used for counting. -/
instance instDecIsHP {n : ℕ} (T : Tournament n) (σ : Equiv.Perm (Fin n)) :
    Decidable (IsHamiltonPath T σ) := by
  unfold IsHamiltonPath; exact inferInstance

end SzeleTournament
