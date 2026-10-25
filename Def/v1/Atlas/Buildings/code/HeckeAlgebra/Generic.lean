/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/Generic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length
import Structure.v1.Atlas.Buildings.code.HeckeAlgebra.Generic


namespace HeckeAlgebra

variable {B : Type*} {W : Type*} [Group W] {M : CoxeterMatrix B}

variable {R : Type*} [CommRing R]

/-- The structure constants are conjugacy-invariant if conjugate simple reflections
have equal $(a_s, b_s)$ values. -/
def StructureConstants.ConjugacyInvariant (sc : StructureConstants B R)
    (cs : CoxeterSystem M W) : Prop :=
  ∀ (s₁ s₂ : B) (w : W), w * cs.simple s₁ * w⁻¹ = cs.simple s₂ →
    sc.a s₁ = sc.a s₂ ∧ sc.b s₁ = sc.b s₂

end HeckeAlgebra
