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
import Structure.v1.Atlas.LieGroups.code.HeckeKL


noncomputable section

open Polynomial

attribute [instance] CoxeterGroupData.grpInst CoxeterGroupData.finInst
  CoxeterGroupData.decEq

instance (C : CoxeterGroupData) (y w : C.W) : Decidable (C.bruhatLE y w) :=
  C.bruhatLE_dec y w

end
