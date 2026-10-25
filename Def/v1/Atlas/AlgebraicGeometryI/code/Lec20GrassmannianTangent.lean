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
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec20GrassmannianTangent
set_option maxHeartbeats 400000

open KaehlerDifferential Module


noncomputable section

universe u v w

section Proposition35

variable (R : Type u) [CommRing R]

variable (A : Type v) [CommRing A] [Algebra R A]

/-- The standard basis `(dx_0, …, dx_n)` of `Ω_{k[x_0,…,x_n]/k}` as a free module of
rank `n + 1`. -/
def euler_seq_kahler_basis :
    Basis (Fin (n + 1)) (PolyRingLec20 k n) (Ω[PolyRingLec20 k n⁄k]) :=
  KaehlerDifferential.mvPolynomialBasis k (Fin (n + 1))

end Proposition35
end
