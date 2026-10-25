/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HeckeKL.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Def.v1.Atlas.LieGroups.code.CompositionSeries
import Lemma.Int.StandardFiltrationMultiplicity.eq.DimHomProjectiveContragredientVerma
import Abbrev.v1.Atlas.LieGroups.code.HeckeKL.Part4


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
