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
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec20GrassmannianTangent
set_option maxHeartbeats 400000

open KaehlerDifferential Module


noncomputable section

universe u v w

section Proposition35

variable (R : Type u) [CommRing R]

variable (A : Type v) [CommRing A] [Algebra R A]

/-- The module of Kähler differentials of `k[x_0,…,x_n]` is free. -/
instance euler_seq_kahler_free :
    Module.Free (PolyRingLec20 k n) (Ω[PolyRingLec20 k n⁄k]) :=
  inferInstance

/-- The module of Kähler differentials of `k[x_0,…,x_n]` is finitely generated. -/
instance euler_seq_kahler_finite :
    Module.Finite (PolyRingLec20 k n) (Ω[PolyRingLec20 k n⁄k]) :=
  Module.Finite.of_basis (euler_seq_kahler_basis k n)

end Proposition35
end
