/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.EpiMono
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.Widesubcategory


namespace AlgebraicTopologyI

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-- **Definition 4.2 (Simplicial object).**  A simplicial object in a
category `C` is a functor `Δ^{op} → C` from the opposite of the simplex
category.  This is a thin wrapper around Mathlib's
`CategoryTheory.SimplicialObject`. -/
abbrev SimplicialObject (C : Type u) [Category.{v} C] := CategoryTheory.SimplicialObject C

/-- **Definition 4.3 (Injective simplex category).**  The wide subcategory
of `SimplexCategory` whose morphisms are the injective (monomorphism)
simplex maps.  Equivalent to the subcategory of strictly order-preserving
maps `[m] → [n]`. -/
abbrev SimplexCategoryInj :=
  WideSubcategory (MorphismProperty.monomorphisms SimplexCategory)

/-- **Definition 4.5 (Split epimorphism).**  A morphism `f : A ⟶ B` is a
*split epimorphism* if it admits a right inverse, i.e. there exists
`s : B ⟶ A` with `s ≫ f = 𝟙 B`.  Thin wrapper around
`CategoryTheory.IsSplitEpi`. -/
abbrev IsSplitEpi {A B : C} (f : A ⟶ B) := CategoryTheory.IsSplitEpi f

/-- **Definition 4.5 (Split monomorphism).**  A morphism `f : X ⟶ Y` is a
*split monomorphism* if it admits a left inverse, i.e. there exists
`r : Y ⟶ X` with `f ≫ r = 𝟙 X`.  Thin wrapper around
`CategoryTheory.SplitMono`. -/
abbrev SplitMonomorphism {X Y : C} (f : X ⟶ Y) := CategoryTheory.SplitMono f

end AlgebraicTopologyI
