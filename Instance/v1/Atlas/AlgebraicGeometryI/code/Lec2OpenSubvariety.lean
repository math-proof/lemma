/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2OpenSubvariety.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.NoetherianSpace
public import Instance.v1.Atlas.AlgebraicGeometryI.code.Lec2AlgebraicVariety
@[expose] public section

namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-- The structure map making an open subscheme of `X` into a scheme over `Spec k`, obtained
by composing the open immersion with the structure map of `X`. -/
noncomputable instance openSubschemeOverSpec (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] (U : X.Opens) :
    (↑U : Scheme.{u}).Over (Spec (.of k)) :=
  OverClass.ofHom (U.ι ≫ (X ↘ Spec (.of k)))

end AlgebraicGeometry.Scheme
