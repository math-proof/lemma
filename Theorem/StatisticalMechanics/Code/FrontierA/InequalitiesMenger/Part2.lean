/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/InequalitiesMenger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc19menger.Part5
import Def.StatisticalMechanics.Code.FrontierA.InequalitiesMenger.Part2
open Finset SimpleGraph


namespace StatMech.FrontierA

open Walls

variable {V : Type*} [Fintype V]


theorem finiteABPackingSizes_nonempty (G : SimpleGraph V) (A B : Set V) :
    (finiteABPackingSizes G A B).Nonempty := by
  classical
  let k : Fin (Fintype.card V + 1) := ⟨0, Nat.zero_lt_succ _⟩
  refine ⟨k, ?_⟩
  simp only [finiteABPackingSizes, Finset.mem_filter, Finset.mem_univ, true_and]
  exact bc17_hard_zero G A B


end StatMech.FrontierA
