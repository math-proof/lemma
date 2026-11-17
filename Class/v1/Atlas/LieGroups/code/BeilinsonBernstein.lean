module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.Adjoin.Basic
public import Def.v1.Atlas.LieGroups.code.BeilinsonBernstein
public section

open CategoryTheory


namespace BeilinsonBernstein

noncomputable section

universe u

attribute [instance] CAlgebra.instRing CAlgebra.instAlgebra

attribute [instance] AbCat.instCat

attribute [instance] GradedAlgebra.instRing GradedAlgebra.instAlgebra

class IsDaffine (X : SmoothAlgVariety.{u}) (DMod : AbCat.{u}) (DXMod : AbCat.{u})
    (Gamma : DMod.Obj ⥤ DXMod.Obj) (Loc : DXMod.Obj ⥤ DMod.Obj) : Prop where
  equiv : ∃ e : DMod.Obj ≌ DXMod.Obj, e.functor = Gamma ∧ e.inverse = Loc

end
end BeilinsonBernstein
