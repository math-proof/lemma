/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section30.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
public import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
public import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
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
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section30.Part3
open Matrix


public noncomputable section

namespace SurfacesAndBilinearForms

open CategoryTheory AlgebraicTopology SingularCohomology

attribute [instance] CompactSurface.compact CompactSurface.connected
  CompactSurface.t2 CompactSurface.charted

/-- The connected sum endows the set of homeomorphism classes of compact
surfaces with the structure of a commutative monoid. -/
structure NondegenSymmBilinFormF2 where
  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module (ZMod 2) V]
  [instFiniteDimensional : FiniteDimensional (ZMod 2) V]
  form : @LinearMap.BilinForm (ZMod 2) _ V instAddCommGroup.toAddCommMonoid instModule
  isSymm : form.IsSymm
  isNondeg : form.Nondegenerate

end SurfacesAndBilinearForms
end
