/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SevenFamilies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Coxeter.Basic
public import Def.v1.Atlas.Buildings.code.CoxeterGroup.TypeACoxeterSystem.Part2
public import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.TypeAInjectivityHelper
public import Def.v1.Atlas.Buildings.code.CoxeterGroup.SignedPermGroup.Part2
public import Def.v1.Atlas.Buildings.code.CoxeterGroup.TypeCInjectivityHelper
public import Def.v1.Atlas.Buildings.code.CoxeterGroup.SevenFamilies
@[expose] public section

/-- The affine-$B$ adjacency predicate is decidable. -/
instance (i j : ℕ) : Decidable (affinBCond i j) := by unfold affinBCond; infer_instance

