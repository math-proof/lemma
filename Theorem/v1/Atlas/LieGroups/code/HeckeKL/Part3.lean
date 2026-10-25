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
import Def.v1.Atlas.LieGroups.code.HeckeKL.Part6


noncomputable section

open Polynomial

attribute [instance] CoxeterGroupData.grpInst CoxeterGroupData.finInst
  CoxeterGroupData.decEq

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

theorem HeckeAlgebra.D_zero (C : CoxeterGroupData) :
    HeckeAlgebra.D C 0 = 0 := by
  unfold HeckeAlgebra.D
  exact Finsupp.sum_zero_index

attribute [-instance] HeckeAlgebra.instRing HeckeAlgebra.instAlgebra in

theorem HeckeAlgebra.D_add (C : CoxeterGroupData)
    (f g : HeckeAlgebra C) :
    HeckeAlgebra.D C (f + g) = HeckeAlgebra.D C f + HeckeAlgebra.D C g := by
  show (f + g).sum (fun w aw => coeffInvolution aw • D_on_basis C w) =
    f.sum (fun w aw => coeffInvolution aw • D_on_basis C w) +
    g.sum (fun w aw => coeffInvolution aw • D_on_basis C w)
  apply Finsupp.sum_add_index'
  · intro i; simp [coeffInvolution_zero]
  · intro i b₁ b₂
    show coeffInvolution (b₁ + b₂) • D_on_basis C i =
      coeffInvolution b₁ • D_on_basis C i + coeffInvolution b₂ • D_on_basis C i
    rw [coeffInvolution_add, add_smul]

end
