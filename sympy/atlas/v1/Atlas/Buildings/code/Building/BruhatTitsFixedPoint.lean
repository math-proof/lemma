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

set_option maxHeartbeats 400000

open Set Filter Topology

noncomputable section

variable {M : Type*} [MetricSpace M]

/-- CAT(0)/negative curvature inequality on a metric space $M$: for every pair $x, y \in M$ there
exists a midpoint $m$ such that for all $z$,
$d(z, m)^2 \leq \tfrac{1}{2} d(z, x)^2 + \tfrac{1}{2} d(z, y)^2 - \tfrac{1}{4} d(x, y)^2$. -/
def NegativeCurvatureInequality (M : Type*) [MetricSpace M] : Prop :=
  ∀ x y : M, ∃ m : M, ∀ z : M,
    dist z m ^ 2 ≤ (1 / 2) * dist z x ^ 2 + (1 / 2) * dist z y ^ 2 - (1 / 4) * dist x y ^ 2

/-- Radius of the set $Y$ as seen from the point $x$: $\sup_{y \in Y} d(x, y)$. -/
def radiusFrom (x : M) (Y : Set M) : ℝ :=
  ⨆ y : Y, dist x (y : M)

/-- Circumradius of $Y$: $\inf_{x \in M} \sup_{y \in Y} d(x, y)$. -/
def circumradius (Y : Set M) : ℝ :=
  ⨅ x : M, radiusFrom x Y

/-- $x$ is a circumcenter of $Y$ iff its enclosing radius equals the circumradius of $Y$. -/
def IsCircumcenter (x : M) (Y : Set M) : Prop :=
  radiusFrom x Y = circumradius Y

/-- An isometric action of a group $G$ on a metric space $M$: a scalar multiplication
respecting the group identity, composition, and acting by isometries on $M$. -/
structure IsometricAction (G : Type*) [Group G] (M : Type*) [MetricSpace M] where
  smul : G → M → M
  smul_one : ∀ x : M, smul 1 x = x
  smul_mul : ∀ (g h : G) (x : M), smul (g * h) x = smul g (smul h x)
  isometry_smul : ∀ g : G, Isometry (smul g)

/-- A subset $Y \subseteq M$ is stable under the isometric action iff $g \cdot Y \subseteq Y$ for
every $g \in G$. -/
def IsometricAction.IsStable {G : Type*} [Group G] (act : IsometricAction G M)
    (Y : Set M) : Prop :=
  ∀ g : G, ∀ y ∈ Y, act.smul g y ∈ Y

/-- $x$ is a fixed point of the isometric action iff $g \cdot x = x$ for all $g \in G$. -/
def IsometricAction.IsFixedPoint {G : Type*} [Group G] (act : IsometricAction G M)
    (x : M) : Prop :=
  ∀ g : G, act.smul g x = x
