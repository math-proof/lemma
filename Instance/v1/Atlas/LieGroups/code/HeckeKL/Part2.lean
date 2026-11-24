module
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Def.v1.Atlas.LieGroups.code.CompositionSeries
public import Theorem.Int.StandardFiltrationMultiplicity.eq.DimHomProjectiveContragredientVerma
public import Abbrev.v1.Atlas.LieGroups.code.HeckeKL.Part3


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

instance HeckeAlgebra.instAddCommMonoid (C : CoxeterGroupData) :
    AddCommMonoid (HeckeAlgebra C) := Finsupp.instAddCommMonoid

instance HeckeAlgebra.instAddCommGroup (C : CoxeterGroupData) :
    AddCommGroup (HeckeAlgebra C) := Finsupp.instAddCommGroup

instance HeckeAlgebra.instModule (C : CoxeterGroupData) :
    Module HeckeCoeffRing (HeckeAlgebra C) := Finsupp.module C.W HeckeCoeffRing

end
