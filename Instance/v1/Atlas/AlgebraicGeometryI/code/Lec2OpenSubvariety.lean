/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2OpenSubvariety.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.NoetherianSpace
import Instance.v1.Atlas.AlgebraicGeometryI.code.Lec2AlgebraicVariety


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
