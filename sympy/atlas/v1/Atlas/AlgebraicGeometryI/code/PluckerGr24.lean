/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PluckerGr24.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dimension.Finrank
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec4Grassmannian
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.Lec4Grassmannian
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.GrassmannianProjective
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.GrassmannianProjective

open ExteriorAlgebra

namespace PluckerGr24

section Anticommutativity

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- A 2-vector ω is decomposable if it can be written as v_1 ∧ v_2 for some vectors. -/
def IsDecomposable2 (ω : ExteriorAlgebra R M) : Prop :=
  ∃ v₁ v₂ : M, ω = ι R v₁ * ι R v₂
