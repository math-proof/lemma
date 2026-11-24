module
public import Def.v1.Atlas.ArithmeticGeometry.code.RiemannRoch.Part6
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.RiemannRoch
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Def.v1.Atlas.ArithmeticGeometry.code.AdeleQuotientDim
open scoped RestrictedProduct
open FunctionFieldAdeleRing DiscreteValuationFamily


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdeleQuotientDim.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
section ChainFormula

variable {R : Type*} [DivisionRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Pullback of $A(A)$ to $A(B)$ as a $k$-submodule: the comap of $A(A)$
along the inclusion $A(B) \hookrightarrow $ adeles. -/
noncomputable abbrev adeleComap (A B : P → ℤ) :
    Submodule k (↥(adeleSpace (F := F) (O := O) k B)) :=
  Submodule.comap (adeleSpace (F := F) (O := O) k B).subtype
    (adeleSpace (F := F) (O := O) k A)

end ChainFormula
