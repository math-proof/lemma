/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PluckerGr24.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Def.v1.Atlas.AlgebraicGeometryI.code.Lec4Grassmannian
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.Lec4Grassmannian
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.GrassmannianProjective
public import Def.v1.Atlas.AlgebraicGeometryI.code.GrassmannianProjective.Part2

@[expose] public section

open ExteriorAlgebra


namespace PluckerGr24

section Anticommutativity

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- A 2-vector ω is decomposable if it can be written as v_1 ∧ v_2 for some vectors. -/
def IsDecomposable2 (ω : ExteriorAlgebra R M) : Prop :=
  ∃ v₁ v₂ : M, ω = ι R v₁ * ι R v₂

end Anticommutativity
end PluckerGr24
