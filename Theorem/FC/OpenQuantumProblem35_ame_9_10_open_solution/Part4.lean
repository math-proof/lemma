/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.FC.OpenQuantumProblem35_ame_9_10_open_solution.Part5
open scoped BigOperators


namespace OpenQuantumProblem35

set_option maxHeartbeats 0

set_option maxRecDepth 100000

@[simp] lemma liftPhysicalSet_card (A : Finset (Fin 9)) :
    (liftPhysicalSet A).card = A.card + 1 := by
  rw [liftPhysicalSet, Finset.card_union_of_disjoint]
  · simp
    omega
  · simp [Finset.disjoint_left]

@[simp] lemma liftPhysicalSet_zero (A : Finset (Fin 9)) :
    (0 : Fin 10) ∈ liftPhysicalSet A := by simp [liftPhysicalSet]

@[simp] lemma liftPhysicalSet_succ (A : Finset (Fin 9)) (i : Fin 9) :
    Fin.succ i ∈ liftPhysicalSet A ↔ i ∈ A := by
  simp [liftPhysicalSet]

end OpenQuantumProblem35
