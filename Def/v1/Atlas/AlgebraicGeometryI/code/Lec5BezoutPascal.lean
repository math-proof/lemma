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
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec5BezoutPascal

@[expose] public section

open MvPolynomial Classical


noncomputable section

namespace Lec5BezoutPascal

variable (k : Type*) [Field k]

/-- A point `p ∈ P^2` lies on the curve defined by a polynomial `f` if `f` vanishes on a (any)
representative of `p`. -/
def P2.liesOn (p : P2 k) (f : MvPolynomial (Fin 3) k) : Prop :=
  MvPolynomial.eval (Projectivization.rep p) f = 0

/-- Translate of a polynomial `g` by a point `p`: the polynomial obtained by substituting
`x_i ↦ x_i + p_i`. -/
def translatePoly {n : ℕ} (g : MvPolynomial (Fin n) k) (p : Fin n → k) :
    MvPolynomial (Fin n) k :=
  MvPolynomial.aeval (fun i => X i + C (p i)) g

end Lec5BezoutPascal
end
