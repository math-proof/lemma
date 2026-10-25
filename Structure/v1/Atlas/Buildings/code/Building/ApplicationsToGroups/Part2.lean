/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ApplicationsToGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.Affine.Part2
import Def.v1.Atlas.Buildings.code.BNPair.ParabolicDefs.Part2
import Lemma.Nat.NonemptyBruhatCell
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Topology.Algebra.OpenSubgroup
import Def.v1.Atlas.Buildings.code.Building.ApplicationsToGroups
set_option linter.unusedSectionVars false

open ChamberComplex


section Parahorics

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

/-- A "parabolic subgroup at infinity" of $G$: a subgroup that is parabolic with
respect to the BN-pair, conceptually corresponding to a parabolic associated to
the spherical building at infinity of an affine building. -/
structure ParabolicSubgroupAtInfinity (G : Type*) [Group G] {B_idx : Type*}
    (M : CoxeterMatrix B_idx) where
  bnpair : BNPair G M
  subgroup : Subgroup G
  isParabolic : bnpair.IsParabolic subgroup

end Parahorics
