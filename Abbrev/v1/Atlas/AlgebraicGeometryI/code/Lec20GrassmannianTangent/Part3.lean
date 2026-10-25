/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianTangent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Grassmannian
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Trace
import Instance.v1.Atlas.AlgebraicGeometryI.code.Lec20GrassmannianTangent.Part2
set_option maxHeartbeats 400000

open KaehlerDifferential Module


noncomputable section

universe u v w

section Proposition35

variable (R : Type u) [CommRing R]

variable (A : Type v) [CommRing A] [Algebra R A]

/-- Tangent space of the Grassmannian at a point `V`, identified with `Hom(V, W/V)`. -/
abbrev grassmannianTangentSpace (kk : ℕ) (V : Module.Grassmannian F W kk) :=
  V.toSubmodule →ₗ[F] (W ⧸ V.toSubmodule)

/-- Cotangent space of the Grassmannian at a point `V`, identified with `Hom(W/V, V)`. -/
abbrev grassmannianCotangentSpace (kk : ℕ) (V : Module.Grassmannian F W kk) :=
  (W ⧸ V.toSubmodule) →ₗ[F] V.toSubmodule

end Proposition35
end
