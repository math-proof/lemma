/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5BezoutPascal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutMultiplicitySum.Part2
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.BezoutMultiplicitySum
public import Def.v1.Atlas.AlgebraicGeometryI.code.Lec5BezoutPascal.Part3
open MvPolynomial Classical


public noncomputable section

namespace Lec5BezoutPascal

variable (k : Type*) [Field k]

/-- A plane projective curve in `P^2`: a nonzero homogeneous polynomial in three variables of a
given degree. -/
structure PlaneCurve where
  poly : MvPolynomial (Fin 3) k
  poly_ne_zero : poly ≠ 0
  deg : ℕ
  poly_homogeneous : poly.IsHomogeneous deg

end Lec5BezoutPascal
end
