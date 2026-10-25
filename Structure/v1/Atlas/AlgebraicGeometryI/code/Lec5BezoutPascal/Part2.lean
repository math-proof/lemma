/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5BezoutPascal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutMultiplicitySum.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.BezoutMultiplicitySum
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec5BezoutPascal.Part4
open MvPolynomial Classical


noncomputable section

namespace Lec5BezoutPascal

variable (k : Type*) [Field k]

/-- Data of a hexagon inscribed in a conic: the conic, six distinct vertices on it, indexed
cyclically by `Fin 6`. -/
structure PascalInscribedHexagon where
  conic : PlaneCurve k
  is_conic : IsConic k conic
  vertex : Fin 6 → P2 k
  vertices_on_conic : ∀ i, P2.liesOn k (vertex i) conic.poly
  vertices_distinct : Function.Injective vertex

end Lec5BezoutPascal
end
