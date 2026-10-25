/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Abbrev.v1.Atlas.NumberTheoryI.code.GroupCohomology.Part6


noncomputable section

open CategoryTheory

universe u

namespace LongExactDerived

open CategoryTheory

universe v

variable {R : Type v} [Ring R]

def homotopyOp {ι : Type*} {V : Type*} [Category V] [Preadditive V]
    {c : ComplexShape ι} {C D : HomologicalComplex V c}
    {f g : C ⟶ D} (h : Homotopy f g) : Homotopy
    ((opFunctor V c).map f.op)
    ((opFunctor V c).map g.op) where
  hom i j := (h.hom j i).op
  zero i j hij := by
    have := h.zero j i hij
    rw [this]
    exact Limits.op_zero _ _
  comm i := by
    have H := h.comm i
    dsimp [dNext, prevD] at H ⊢
    change (f.f i).op =
      (h.hom i (c.prev i) ≫ D.d (c.prev i) i).op +
      (C.d i (c.next i) ≫ h.hom (c.next i) i).op +
      (g.f i).op
    rw [H]
    simp only [op_add, add_comm]

noncomputable def homStarFunctor (A : ModuleCat.{v} R) :
    (ChainComplexDef.ChainComplexRMod R)ᵒᵖ ⥤
    HomologicalComplex AddCommGrpCat.{v} (ComplexShape.down ℕ).symm :=
  opFunctor _ _ ⋙ (preadditiveYoneda.obj A).mapHomologicalComplex _

end LongExactDerived
end
