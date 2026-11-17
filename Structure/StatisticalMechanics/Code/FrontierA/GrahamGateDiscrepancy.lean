/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Max
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part4


public section

namespace StatMech.FrontierA

structure RelationPartialMatching {A B : Type*} (r : A -> B -> Prop) where
  toFun : A -> Option B
  related : ∀ {a b}, toFun a = some b -> r a b
  injective_some : ∀ {a₁ a₂ b},
    toFun a₁ = some b -> toFun a₂ = some b -> a₁ = a₂

end StatMech.FrontierA
