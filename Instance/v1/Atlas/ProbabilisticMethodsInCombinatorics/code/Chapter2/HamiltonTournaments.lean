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
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter2.HamiltonTournaments
set_option maxHeartbeats 800000

open Finset Fintype


namespace SzeleTournament

/-- Decidability instance for `IsHamiltonPath`, used for counting. -/
instance instDecIsHP {n : ℕ} (T : Tournament n) (σ : Equiv.Perm (Fin n)) :
    Decidable (IsHamiltonPath T σ) := by
  unfold IsHamiltonPath; exact inferInstance

end SzeleTournament
