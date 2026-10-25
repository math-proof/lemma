/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3Morphisms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec3Morphisms


noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace VarietyMorphism

variable {X Y Z : Scheme.{u}}

section ContinuousMap

/-- Pullback of regular sections along a morphism: a function on `U ⊆ Y` pulls back to a function
on the preimage `f⁻¹(U) ⊆ X`. -/
def pullbackSections (f : VarietyMorphism X Y) (U : Y.Opens) :
    Γ(Y, U) ⟶ Γ(X, f ⁻¹ᵁ U) :=
  f.app U

/-- Pullback of global regular sections along a morphism of varieties. -/
def pullbackGlobal (f : VarietyMorphism X Y) :
    Γ(Y, ⊤) ⟶ Γ(X, ⊤) :=
  f.appTop

end PullbackRegular

section Functoriality

/-- The underlying morphism of locally ringed spaces of a morphism of varieties. -/
def toLocallyRingedSpaceHom (f : VarietyMorphism X Y) :
    X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace :=
  f.toLRSHom

end Functoriality
end VarietyMorphism
end
