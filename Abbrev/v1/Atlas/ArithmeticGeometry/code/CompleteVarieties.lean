/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CompleteVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.KrullDimension.Zero
@[expose] public section

universe u


/-- A variety is a topological space that is Noetherian (every descending chain of closed subsets stabilizes). -/
abbrev IsVariety (X : Type u) [TopologicalSpace X] : Prop :=
  TopologicalSpace.NoetherianSpace X

