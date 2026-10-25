/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/KahlerManifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds.Part4
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AlmostComplexManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ArnoldConjecture
import Class.v1.Atlas.GeometryOfManifolds.code.ArnoldConjecture.Part4
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Structure.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds
set_option autoImplicit false


noncomputable section

open scoped Manifold


section MfdKahler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

variable {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The Nijenhuis tensor field of an almost complex structure $J$: $N_J(U,V) = [JU, JV] - J[U, JV] - J[JU, V] - [U, V]$. -/
def nijenhuisTensorField [IsManifold I ⊤ M]
    (Jstr : AlmostComplexStructure I M)
    (U V : ∀ (x : M), TangentSpace I x) (x : M) : TangentSpace I x :=
  let JU : ∀ y : M, TangentSpace I y := fun y => Jstr.J y (U y)
  let JV : ∀ y : M, TangentSpace I y := fun y => Jstr.J y (V y)
  VectorField.mlieBracket I JU JV x
    - Jstr.J x (VectorField.mlieBracket I U JV x)
    - Jstr.J x (VectorField.mlieBracket I JU V x)
    - VectorField.mlieBracket I U V x

end MfdKahler
end
