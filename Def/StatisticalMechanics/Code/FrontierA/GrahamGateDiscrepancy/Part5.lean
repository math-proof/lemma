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
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part5

@[expose] public section

namespace StatMech.FrontierA

def RelationPartialMatching.IsMaximum
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (matching : RelationPartialMatching r) : Prop :=
  ∀ other : RelationPartialMatching r,
    other.support.card ≤ matching.support.card


end StatMech.FrontierA
