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
import Def.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part7


namespace StatMech.FrontierA

theorem RelationPartialMatching.targetPreimage_spec
    {A B : Type*} {r : A -> B -> Prop}
    (matching : RelationPartialMatching r)
    (hsaturated : ∀ b, ∃ a, matching.toFun a = some b) (b : B) :
    matching.toFun (matching.targetPreimage hsaturated b) = some b :=
  Classical.choose_spec (hsaturated b)

theorem RelationPartialMatching.targetPreimage_injective
    {A B : Type*} {r : A -> B -> Prop}
    (matching : RelationPartialMatching r)
    (hsaturated : ∀ b, ∃ a, matching.toFun a = some b) :
    Function.Injective (matching.targetPreimage hsaturated) := by
  intro b c hbc
  apply Option.some.inj
  calc
    some b = matching.toFun (matching.targetPreimage hsaturated b) :=
      (matching.targetPreimage_spec hsaturated b).symm
    _ = matching.toFun (matching.targetPreimage hsaturated c) := congrArg _ hbc
    _ = some c := matching.targetPreimage_spec hsaturated c


end StatMech.FrontierA
