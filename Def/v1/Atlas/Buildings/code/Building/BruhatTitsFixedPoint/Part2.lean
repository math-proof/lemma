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
import Structure.v1.Atlas.Buildings.code.Building.BruhatTitsFixedPoint
set_option maxHeartbeats 400000

open Set Filter Topology


noncomputable section

variable {M : Type*} [MetricSpace M]

/-- A subset $Y \subseteq M$ is stable under the isometric action iff $g \cdot Y \subseteq Y$ for
every $g \in G$. -/
def IsometricAction.IsStable {G : Type*} [Group G] (act : IsometricAction G M)
    (Y : Set M) : Prop :=
  ∀ g : G, ∀ y ∈ Y, act.smul g y ∈ Y

/-- $x$ is a fixed point of the isometric action iff $g \cdot x = x$ for all $g \in G$. -/
def IsometricAction.IsFixedPoint {G : Type*} [Group G] (act : IsometricAction G M)
    (x : M) : Prop :=
  ∀ g : G, act.smul g x = x

end
