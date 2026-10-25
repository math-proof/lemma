/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRawNonbacktrackingSimple.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveVertexConnector.Part2


namespace StatMech.FrontierA

open scoped Convex

open Set

theorem fin_add_one_plus_one
    {n : ℕ} [NeZero n] (i : Fin n) :
    i + (1 + 1) = i + 2 := by
  have hone : (1 : Fin n) + 1 = 2 := by
    apply Fin.ext
    change (1 % n + 1 % n) % n = 2 % n
    rw [← Nat.add_mod]
  exact congrArg (fun q : Fin n ↦ i + q) hone

theorem fin_add_one_add_one
    {n : ℕ} [NeZero n] (i : Fin n) :
    i + 1 + 1 = i + 2 :=
  (add_assoc i 1 1).trans (fin_add_one_plus_one i)


end StatMech.FrontierA
