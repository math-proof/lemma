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
import Abbrev.v1.Atlas.ArithmeticGeometry.code.CompleteVarieties
universe u


/-- A complete variety: a variety $X$ such that the second projection $X \times Y \to Y$ is a closed map for every variety $Y$ (the topological analog of properness). -/
class IsCompleteVariety (X : Type u) [TopologicalSpace X] : Prop where
  isVariety : IsVariety X
  isClosedMap_snd : ∀ (Y : Type u) [TopologicalSpace Y] [IsVariety Y],
    IsClosedMap (Prod.snd : X × Y → Y)

