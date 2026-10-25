/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DixmierLemma.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Theorem.v1.Atlas.LieGroups.code.DixmierLemma


noncomputable section

open Polynomial Finset Classical Finsupp Cardinal

universe u


instance endDivisionRing {A : Type u} [Ring A]
    {M : Type u} [AddCommGroup M] [Module A M]
    [IsSimpleModule A M] : DivisionRing (Module.End A M) :=
  haveI : Nontrivial M := IsSimpleModule.nontrivial A M
  { (inferInstance : Ring (Module.End A M)) with
    inv := fun f => if h : f = 0 then 0 else
      (LinearEquiv.ofBijective f (endomorphism_bijective_of_ne_zero f h)).symm.toLinearMap
    inv_zero := by simp
    mul_inv_cancel := by
      intro f hf; simp only [dif_neg hf]; ext x
      show f ((LinearEquiv.ofBijective f (endomorphism_bijective_of_ne_zero f hf)).symm x) = x
      exact (LinearEquiv.ofBijective f _).apply_symm_apply x
    nnqsmul := _
    qsmul := _ }


end
