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
import Def.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy


namespace StatMech.FrontierA

@[simp] theorem mem_functionWeakComponent_self
    {B : Type*} (next : B -> B) (x : B) :
    x ∈ functionWeakComponent next x :=
  Relation.EqvGen.refl x

theorem functionWeakComponent_eq_of_mem
    {B : Type*} (next : B -> B) {x y : B}
    (hxy : y ∈ functionWeakComponent next x) :
    functionWeakComponent next x = functionWeakComponent next y := by
  ext z
  constructor
  · intro hxz
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ hxy) hxz
  · intro hyz
    exact Relation.EqvGen.trans _ _ _ hxy hyz

@[simp] theorem functionWeakComponent_next
    {B : Type*} (next : B -> B) (x : B) :
    functionWeakComponent next (next x) = functionWeakComponent next x := by
  symm
  apply functionWeakComponent_eq_of_mem
  exact Relation.EqvGen.rel x (next x) rfl


end StatMech.FrontierA
