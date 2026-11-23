/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ApplicationsToGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.Buildings.code.Building.Affine.Part2
public import Def.v1.Atlas.Buildings.code.BNPair.ParabolicDefs.Part2
public import Theorem.Nat.NonemptyBruhatCell
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Order.Filter.AtTopBot.Group
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Structure.v1.Atlas.Buildings.code.Building.ApplicationsToGroups

@[expose] public section

set_option linter.unusedSectionVars false

open ChamberComplex


section Parahorics

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

/-- The underlying set of a parahoric subgroup, namely the standard parabolic
$P_J$. -/
def ParahoricSubgroup.toSet {G : Type*} [Group G] {B_idx : Type*}
    {M : CoxeterMatrix B_idx} (P : ParahoricSubgroup G M) : Set G :=
  P.bnpair.standardParabolic P.generatorSubset

end Parahorics
