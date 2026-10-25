/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Def.v1.Atlas.LieGroups.code.BeilinsonBernstein
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
