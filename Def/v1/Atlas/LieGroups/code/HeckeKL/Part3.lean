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
import Instance.v1.Atlas.LieGroups.code.HeckeKL.Part3


noncomputable section

open Polynomial

attribute [instance] CoxeterGroupData.grpInst CoxeterGroupData.finInst
  CoxeterGroupData.decEq

def HeckeAlgebra.ofScalar (C : CoxeterGroupData) (a : HeckeCoeffRing) : HeckeAlgebra C :=
  Finsupp.single 1 a

def heckeAlgebraMap (C : CoxeterGroupData) : HeckeCoeffRing →+* HeckeAlgebra C where
  toFun r := Finsupp.single 1 r
  map_one' := rfl
  map_mul' := by
    intro a b
    show Finsupp.single (1 : C.W) (a * b) = heckeMul C (Finsupp.single 1 a) (Finsupp.single 1 b)
    unfold heckeMul
    rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
    rw [Finsupp.sum_single_index (by simp [mul_zero, zero_smul])]
    have hb : heckeMulBasis C 1 1 = Finsupp.single (1 : C.W) 1 := by
      unfold heckeMulBasis
      simp [C.length_one]
    rw [hb, Finsupp.smul_single, smul_eq_mul, mul_one]
  map_zero' := by
    change Finsupp.single (1 : C.W) (0 : HeckeCoeffRing) = 0
    simp
  map_add' := by
    intro a b
    change Finsupp.single (1 : C.W) (a + b) =
      Finsupp.single (1 : C.W) a + Finsupp.single (1 : C.W) b
    rw [Finsupp.single_add]

end
