/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.AlgebraicGeometryI.code.LinearEquivDivisors.Part3
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.LinearEquivDivisors
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.PrincipalDivisorDegree
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.BezoutTheorem
public import Def.v1.Atlas.AlgebraicGeometryI.code.PrincipalDivisorDegree.Part2
public import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutTheorem
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

set_option maxHeartbeats 1600000

open Polynomial Module


noncomputable section

namespace BezoutIntersection

set_option synthInstance.maxHeartbeats 200000 in
/-- Multiplication-by-`X` operator on the quotient `k[X][Y]/⟨f, g⟩`, viewed as a `k`-linear
endomorphism. -/
def mulByXOp (k : Type*) [Field k]
    (f g : Polynomial (Polynomial k)) :
    Module.End k (Polynomial (Polynomial k) ⧸ Ideal.span {f, g}) :=
  (Algebra.lmul k (Polynomial (Polynomial k) ⧸ Ideal.span {f, g}))
    (Ideal.Quotient.mk _ X)

set_option synthInstance.maxHeartbeats 200000 in
/-- Multiplication-by-`Y` operator (i.e. by `C X` in `k[X][Y]`) on the quotient
`k[X][Y]/⟨f, g⟩`, viewed as a `k`-linear endomorphism. -/
def mulByYOp (k : Type*) [Field k]
    (f g : Polynomial (Polynomial k)) :
    Module.End k (Polynomial (Polynomial k) ⧸ Ideal.span {f, g}) :=
  (Algebra.lmul k (Polynomial (Polynomial k) ⧸ Ideal.span {f, g}))
    (Ideal.Quotient.mk _ (C X))

set_option synthInstance.maxHeartbeats 200000 in

/-- Local intersection multiplicity of the affine plane curves `f = 0` and `g = 0` at the
point `(a, b)`, defined as the dimension of the simultaneous generalised eigenspace of the
multiplication-by-`X` and multiplication-by-`Y` operators with eigenvalues `a` and `b`. -/
noncomputable def localIntersectionMultiplicity (k : Type*) [Field k]
    (f g : Polynomial (Polynomial k)) (a b : k) : ℕ :=
  finrank k ↥(
    (mulByXOp k f g).genEigenspace a ⊤ ⊓
    (mulByYOp k f g).genEigenspace b ⊤
      : Submodule k (Polynomial (Polynomial k) ⧸ Ideal.span {f, g}))

/-- Total intersection number of `f` and `g`, equal to the `k`-dimension of the quotient
`k[X][Y]/⟨f, g⟩`. Bezout's theorem identifies this with `deg(f) · deg(g)`. -/
def totalIntersectionNumber (k : Type*) [Field k]
    (f g : Polynomial (Polynomial k)) : ℕ :=
  finrank k (Polynomial (Polynomial k) ⧸ Ideal.span {f, g})

end BezoutIntersection
end
