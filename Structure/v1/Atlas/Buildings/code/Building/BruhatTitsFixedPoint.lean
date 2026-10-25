/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/BruhatTitsFixedPoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Sqrt
import Def.v1.Atlas.Buildings.code.Building.BruhatTitsFixedPoint
set_option maxHeartbeats 400000

open Set Filter Topology


noncomputable section

variable {M : Type*} [MetricSpace M]

/-- An isometric action of a group $G$ on a metric space $M$: a scalar multiplication
respecting the group identity, composition, and acting by isometries on $M$. -/
structure IsometricAction (G : Type*) [Group G] (M : Type*) [MetricSpace M] where
  smul : G → M → M
  smul_one : ∀ x : M, smul 1 x = x
  smul_mul : ∀ (g h : G) (x : M), smul (g * h) x = smul g (smul h x)
  isometry_smul : ∀ g : G, Isometry (smul g)

end
