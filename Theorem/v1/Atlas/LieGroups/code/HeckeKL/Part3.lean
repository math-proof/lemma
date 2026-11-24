module
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Def.v1.Atlas.LieGroups.code.CompositionSeries
public import Theorem.Int.StandardFiltrationMultiplicity.eq.DimHomProjectiveContragredientVerma
public import Def.v1.Atlas.LieGroups.code.HeckeKL.Part6


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
