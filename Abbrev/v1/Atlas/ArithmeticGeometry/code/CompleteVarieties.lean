/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CompleteVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.KrullDimension.Zero
universe u


/-- A variety is a topological space that is Noetherian (every descending chain of closed subsets stabilizes). -/
abbrev IsVariety (X : Type u) [TopologicalSpace X] : Prop :=
  TopologicalSpace.NoetherianSpace X

