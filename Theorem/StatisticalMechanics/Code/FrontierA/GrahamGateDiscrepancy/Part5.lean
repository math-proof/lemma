/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Def.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part4


namespace StatMech.FrontierA

@[simp] theorem RelationPartialMatching.mem_support_iff
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (matching : RelationPartialMatching r) (a : A) :
    a ∈ matching.support ↔ ∃ b, matching.toFun a = some b := by
  classical
  simp only [RelationPartialMatching.support, Finset.mem_filter,
    Finset.mem_univ, true_and, Option.isSome_iff_exists]


end StatMech.FrontierA
