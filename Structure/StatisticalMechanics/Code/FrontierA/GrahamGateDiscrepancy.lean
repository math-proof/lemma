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
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part4


namespace StatMech.FrontierA

structure RelationPartialMatching {A B : Type*} (r : A -> B -> Prop) where
  toFun : A -> Option B
  related : ∀ {a b}, toFun a = some b -> r a b
  injective_some : ∀ {a₁ a₂ b},
    toFun a₁ = some b -> toFun a₂ = some b -> a₁ = a₂

end StatMech.FrontierA
