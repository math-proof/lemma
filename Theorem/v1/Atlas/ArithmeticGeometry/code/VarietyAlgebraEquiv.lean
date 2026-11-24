module
public import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part5
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.AffineVarieties
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
public import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part9
public import Def.v1.Atlas.ArithmeticGeometry.code.VarietyAlgebraEquiv


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/VarietyAlgebraEquiv.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

variable (k : Type*) [Field k]

open MvPolynomial

/-- Evaluating the class of $g$ in the coordinate ring gives $g(P)$. -/
@[simp]
theorem evalOnCoordRing_mk {n : ℕ} (X : Set (Fin n → AlgebraicClosure k))
    (P : Fin n → AlgebraicClosure k) (hP : P ∈ X)
    (g : MvPolynomial (Fin n) (AlgebraicClosure k)) :
    evalOnCoordRing k X P hP (Ideal.Quotient.mk (idealOfAlgebraicSet X) g) =
    MvPolynomial.eval P g :=
  rfl

end
