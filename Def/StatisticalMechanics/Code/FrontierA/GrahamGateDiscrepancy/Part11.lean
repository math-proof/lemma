module
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Max
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part12


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

noncomputable def RelationPartialMatching.HoleState.naturalSupport
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (state : RelationPartialMatching.HoleState r) :
    Finset A := by
  classical
  exact Finset.univ.filter fun a =>
    state.matching.toFun a = some (natural a)


end StatMech.FrontierA
