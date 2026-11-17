/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ReflexiveSheaves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.Ideal.Basic
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.ReflexiveSheaves

@[expose] public section

noncomputable section

namespace ReflexiveSheaf

open Module

section ReflexivityCharacterization

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The double-dual isomorphism `M ≃ M^{∨∨}` packaged as a `LinearEquiv` for
finitely generated projective modules. -/
def doubleDualLocallyFree (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    M ≃ₗ[R] doubleDualSheaf R M :=
  haveI : IsReflexive R M := Module.instIsReflexiveOfFiniteOfProjective R M
  Module.evalEquiv R M

end ReflexivityCharacterization
end ReflexiveSheaf
end
