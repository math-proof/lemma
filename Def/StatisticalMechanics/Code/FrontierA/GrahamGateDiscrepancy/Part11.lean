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
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part12


namespace StatMech.FrontierA

noncomputable def RelationPartialMatching.HoleState.naturalSupport
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (state : RelationPartialMatching.HoleState r) :
    Finset A := by
  classical
  exact Finset.univ.filter fun a =>
    state.matching.toFun a = some (natural a)


end StatMech.FrontierA
