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
import Def.v1.Atlas.Buildings.code.Building.ApplicationsToGroups.Part2
set_option linter.unusedSectionVars false

open ChamberComplex


section TopologicalGroupDefinition

/-- Bundled definition of a topological group: continuous multiplication and
inversion. -/
structure TopologicalGroupDef (G : Type*) [TopologicalSpace G] [Group G] : Prop where
  mul_continuous : Continuous (fun p : G × G => p.1 * p.2)
  inv_continuous : Continuous (Inv.inv : G → G)

end TopologicalGroupDefinition
