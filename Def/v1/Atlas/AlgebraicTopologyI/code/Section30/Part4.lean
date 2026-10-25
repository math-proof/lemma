/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section30.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Projection
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section30.Part2
open Matrix


noncomputable section

namespace SurfacesAndBilinearForms

open CategoryTheory AlgebraicTopology SingularCohomology

attribute [instance] CompactSurface.compact CompactSurface.connected
  CompactSurface.t2 CompactSurface.charted

attribute [instance] NondegenSymmBilinFormF2.instAddCommGroup
  NondegenSymmBilinFormF2.instModule NondegenSymmBilinFormF2.instFiniteDimensional

/-- Two nondegenerate symmetric bilinear forms over `F₂` are *isometric* if
there is a linear isomorphism of the underlying vector spaces that takes
one form to the other. -/
def NondegenSymmBilinFormF2.Isometric (B₁ B₂ : NondegenSymmBilinFormF2) : Prop :=
  ∃ (f : B₁.V ≃ₗ[ZMod 2] B₂.V),
    ∀ (x y : B₁.V), B₂.form (f x) (f y) = B₁.form x y

/-- The set of *isometry classes* of nondegenerate symmetric bilinear forms
over `F₂`. -/
def BilinFormClass : Type 1 := Quot NondegenSymmBilinFormF2.Isometric

/-- The orthogonal direct sum endows the set of isometry classes of
nondegenerate symmetric `F₂`-bilinear forms with the structure of a
commutative monoid. -/
def BilinFormClass.mk : NondegenSymmBilinFormF2 → BilinFormClass := Quot.mk _


/-- The intersection form on `H¹(S; F₂)` of a compact surface is symmetric
(over characteristic 2 the cup product is graded-commutative without sign). -/

end SurfacesAndBilinearForms

section

open LinearMap.BilinForm

namespace BilinearForm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- When `B|_W` is nondegenerate, `V` decomposes as the internal direct
sum `W ⊕ W^⊥`, giving a linear equivalence `W × W^⊥ ≃ₗ V`. -/
noncomputable def orthogonalProdEquiv
    (B : LinearMap.BilinForm K V) (hB_refl : B.IsRefl)
    {W : Submodule K V} (hW : (B.restrict W).Nondegenerate) :
    (↥W × ↥(B.orthogonal W)) ≃ₗ[K] V :=
  Submodule.prodEquivOfIsCompl W (B.orthogonal W)
    (isCompl_orthogonal_of_restrict_nondegenerate hB_refl hW)

end BilinearForm
end
end
