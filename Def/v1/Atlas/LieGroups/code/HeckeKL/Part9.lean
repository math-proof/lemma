module
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Def.v1.Atlas.LieGroups.code.CompositionSeries
public import Theorem.Int.StandardFiltrationMultiplicity.eq.DimHomProjectiveContragredientVerma
public import Abbrev.v1.Atlas.LieGroups.code.HeckeKL.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HeckeKL.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open Polynomial

attribute [instance] CoxeterGroupData.grpInst CoxeterGroupData.finInst
  CoxeterGroupData.decEq

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

def IsDominantRegularWeight
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=

  IsDominantWeightLE rd wg lam ∧

  (∀ w : wg.W, wg.shiftedAction w lam = lam → w = 1)

def polyToHeckeCoeff (p : Polynomial ℤ) : HeckeCoeffRing :=
  p.eval₂ (Int.castRingHom (LaurentPolynomial ℤ)) (LaurentPolynomial.T 2)

def KLBasisElement (C : CoxeterGroupData) (w : C.W) : HeckeAlgebra C :=
  ∑ y : C.W, Finsupp.single y
    (LaurentPolynomial.T (-(C.length w : ℤ)) * polyToHeckeCoeff (KazhdanLusztigPoly C y w))

end
