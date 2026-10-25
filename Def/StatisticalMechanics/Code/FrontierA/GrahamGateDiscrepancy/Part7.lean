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
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part7


namespace StatMech.FrontierA

noncomputable def RelationPartialMatching.targetPreimage
    {A B : Type*} {r : A -> B -> Prop}
    (matching : RelationPartialMatching r)
    (hsaturated : ∀ b, ∃ a, matching.toFun a = some b) (b : B) : A :=
  Classical.choose (hsaturated b)

end StatMech.FrontierA
