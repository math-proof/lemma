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
open CategoryTheory


namespace BeilinsonBernstein

noncomputable section

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
