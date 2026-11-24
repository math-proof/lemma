module
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Def.v1.Atlas.LieGroups.code.CompositionSeries
public import Theorem.Int.StandardFiltrationMultiplicity.eq.DimHomProjectiveContragredientVerma
public import Abbrev.v1.Atlas.LieGroups.code.HeckeKL.Part4


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

def coeffInvolution : HeckeCoeffRing → HeckeCoeffRing :=
  Finsupp.mapDomain (fun (n : ℤ) => -n)

def negAddHom : ℤ →+ ℤ where
  toFun n := -n
  map_zero' := by simp
  map_add' := by intros; simp [neg_add_rev, add_comm]

def coeffInvolutionRingHom : HeckeCoeffRing →+* HeckeCoeffRing :=
  AddMonoidAlgebra.mapDomainRingHom ℤ negAddHom

end
