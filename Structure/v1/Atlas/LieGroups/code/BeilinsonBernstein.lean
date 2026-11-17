/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.Adjoin.Basic
open CategoryTheory


namespace BeilinsonBernstein

public noncomputable section

universe u

structure SmoothAlgVariety where
  carrier : Type u

structure CAlgebra where
  carrier : Type u
  instRing : Ring carrier
  instAlgebra : Algebra ℂ carrier

attribute [instance] CAlgebra.instRing CAlgebra.instAlgebra

structure AbCat where
  Obj : Type u
  instCat : Category Obj

attribute [instance] AbCat.instCat

structure GradedAlgebra where
  carrier : Type u
  instRing : Ring carrier
  instAlgebra : Algebra ℂ carrier

end
end BeilinsonBernstein
