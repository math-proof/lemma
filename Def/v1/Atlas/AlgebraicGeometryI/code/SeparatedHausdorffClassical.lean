/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SeparatedHausdorffClassical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Data.Complex.Basic
public import Mathlib.Topology.Separation.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory


noncomputable section

namespace SeparatedHausdorffClassical

/-- Complex points of a scheme `X`: morphisms `Spec ℂ → X`. -/
def complexPoints (X : Scheme) : Type _ :=
  (Spec (CommRingCat.of ℂ)) ⟶ X

end SeparatedHausdorffClassical
end
