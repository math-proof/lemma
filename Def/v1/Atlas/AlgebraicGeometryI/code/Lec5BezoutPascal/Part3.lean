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
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec5BezoutPascal.Part2
open MvPolynomial Classical


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
