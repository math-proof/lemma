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
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec5BezoutPascal.Part2
open MvPolynomial Classical


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5BezoutPascal.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace Lec5BezoutPascal

variable (k : Type*) [Field k]

/-- Multiplication-by-`x_i` operator on the curve quotient `k[x, y]/(f, g)`, viewed as a
`k`-linear endomorphism. -/
def mulByVarOperator (f g : MvPolynomial (Fin 2) k) (i : Fin 2) :
    Module.End k (CurveQuotient k f g) :=
  Algebra.lmul k _ (Ideal.Quotient.mk _ (X i))

/-- Intersection multiplicity of two affine plane curves at a point `p`: the dimension of the
joint generalized eigenspace of the multiplication-by-coordinate operators at the eigenvalue `p`. -/
def intersectionMultiplicity (f g : MvPolynomial (Fin 2) k) (p : Fin 2 → k)
    [Module.Finite k (CurveQuotient k f g)] : ℕ :=
  Module.finrank k ↥(
    (mulByVarOperator k f g 0).genEigenspace (p 0) ⊤ ⊓
    (mulByVarOperator k f g 1).genEigenspace (p 1) ⊤
      : Submodule k (CurveQuotient k f g))

end Lec5BezoutPascal
end
