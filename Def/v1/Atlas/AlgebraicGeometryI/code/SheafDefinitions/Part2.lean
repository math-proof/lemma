/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafDefinitions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Instance.v1.Atlas.AlgebraicGeometryI.code.SheafDefinitions
set_option linter.unusedVariables false


namespace SheafDefinitions

open CategoryTheory TopologicalSpace

/-- An `O`-module is **locally free of rank `n`** if there is an open cover
`{U_i}` of `X` such that each restriction `M(U_i)` is a free `O(U_i)`-module of
rank `n`. -/
def IsLocallyFree {X : Type*} [TopologicalSpace X]
    (O : (Opens X)ᵒᵖ ⥤ CommRingCat)
    (M : ∀ (U : Opens X), Type*)
    [∀ U, AddCommGroup (M U)]
    [∀ U, Module (O.obj (Opposite.op U)) (M U)]
    (n : ℕ) : Prop :=
  ∃ (ι : Type*) (U : ι → Opens X),
    (⨆ i, U i = ⊤) ∧
    ∀ i, Module.Free (O.obj (Opposite.op (U i))) (M (U i)) ∧
      Module.finrank (O.obj (Opposite.op (U i))) (M (U i)) = n

end SheafDefinitions
