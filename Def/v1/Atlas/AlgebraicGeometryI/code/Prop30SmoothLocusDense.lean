/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop30SmoothLocusDense.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Topology.Basic
public import Mathlib.AlgebraicGeometry.FunctionField

@[expose] public section

noncomputable section

open AlgebraicGeometry IsLocalRing

universe u

/-- The smooth locus of a scheme: points where the local ring is regular. -/
def Scheme.smoothLocus' (X : Scheme.{u}) [IsLocallyNoetherian X] : Set X :=
  {x : X | IsRegularLocalRing (X.presheaf.stalk x)}

end
