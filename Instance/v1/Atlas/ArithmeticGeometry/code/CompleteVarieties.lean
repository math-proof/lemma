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
public import Class.v1.Atlas.ArithmeticGeometry.code.CompleteVarieties

@[expose] public section

universe u


open AlgebraicGeometry in
/-- Compatibility: a complete variety in our topological sense gives a proper morphism to $\mathrm{Spec}(K)$ in the scheme-theoretic sense. -/
instance (priority := 100) IsCompleteVariety.toNoetherianSpace
    {X : Type u} [TopologicalSpace X] [h : IsCompleteVariety X] :
    TopologicalSpace.NoetherianSpace X := h.isVariety

namespace IsCompleteVariety

variable {X : Type u} [TopologicalSpace X]

/-- Any compact Noetherian space is a complete variety, since the projection $X \times Y \to Y$ from a compact space is automatically closed. -/
instance of_compactSpace [CompactSpace X] [TopologicalSpace.NoetherianSpace X] :
    IsCompleteVariety X where
  isVariety := inferInstance
  isClosedMap_snd _ := isClosedMap_snd_of_compactSpace

end IsCompleteVariety
