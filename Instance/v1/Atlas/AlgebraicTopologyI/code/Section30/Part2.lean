module
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Projection
public import Structure.v1.Atlas.AlgebraicTopologyI.code.Section30
open Matrix


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section30.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace SurfacesAndBilinearForms

open CategoryTheory AlgebraicTopology SingularCohomology

/-- Coerce a `CompactSurface` to its underlying `TopCat` object. -/
instance : CoeSort CompactSurface TopCat.{0} := ⟨CompactSurface.toTopCat⟩

attribute [instance] CompactSurface.compact CompactSurface.connected
  CompactSurface.t2 CompactSurface.charted

/-- Make the `C⁰`-manifold structure of a `CompactSurface` available
automatically through typeclass inference. -/
instance (S : CompactSurface) :
    IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) 0 S.toTopCat :=
  S.isManifold


end SurfacesAndBilinearForms
end
