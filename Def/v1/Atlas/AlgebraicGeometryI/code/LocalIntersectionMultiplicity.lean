/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocalIntersectionMultiplicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.LocalIntersectionMultiplicity
set_option maxHeartbeats 400000


noncomputable section

open MvPolynomial Module

namespace LocalIntersection

variable (k : Type*) [Field k]

/-- Multiplication by `x` as a `k`-linear endomorphism of the intersection quotient. -/
def mulByXOp (f g : MvPolynomial (Fin 2) k) :
    End k (IntersectionQuotient k f g) :=
  Algebra.lmul k _ (Ideal.Quotient.mk _ (X 0))

/-- Multiplication by `y` as a `k`-linear endomorphism of the intersection quotient. -/
def mulByYOp (f g : MvPolynomial (Fin 2) k) :
    End k (IntersectionQuotient k f g) :=
  Algebra.lmul k _ (Ideal.Quotient.mk _ (X 1))

/-- The common generalized eigenspace where `x` acts with generalized eigenvalue `a`
and `y` with generalized eigenvalue `b`. -/
def commonGenEigenspace (f g : MvPolynomial (Fin 2) k) (a b : k) :
    Submodule k (IntersectionQuotient k f g) :=
  (mulByXOp k f g).maxGenEigenspace a ⊓ (mulByYOp k f g).maxGenEigenspace b

/-- The local intersection multiplicity of `f` and `g` at the point `(a,b)` is the
`k`-dimension of the common generalized eigenspace (Def 13, Lec 5). -/
def localIntersectionMultiplicity (f g : MvPolynomial (Fin 2) k) (a b : k) : ℕ :=
  finrank k (commonGenEigenspace k f g a b)

/-- The total intersection number of `f` and `g` is the `k`-dimension of the
intersection quotient `k[x,y]/(f,g)`. -/
def totalIntersectionNumberMv (f g : MvPolynomial (Fin 2) k) : ℕ :=
  finrank k (IntersectionQuotient k f g)

end LocalIntersection
end
