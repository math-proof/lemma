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
import Structure.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy


namespace StatMech.FrontierA

noncomputable instance instFintypeRelationPartialMatching
    {A B : Type*} [Fintype A] [Fintype B] (r : A -> B -> Prop) :
    Fintype (RelationPartialMatching r) := by
  classical
  let encode : RelationPartialMatching r -> A -> Option B :=
    fun matching => matching.toFun
  apply Fintype.ofInjective encode
  intro x y h
  cases x
  cases y
  cases h
  rfl


end StatMech.FrontierA
