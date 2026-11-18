module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DistinguishedInvertible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.CategoryTheory.Yoneda
public import Instance.v1.Atlas.TensorCategories.code.InvertibleObjects
public import Structure.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
public import Def.v1.Atlas.TensorCategories.code.CategoricalFreeness.Part2
public import Def.v1.Atlas.TensorCategories.code.DistinguishedInvertible
public section
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category Limits TensorCategories

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

variable (C) in
/-- Data of a distinguished invertible object `L_ρ ∈ C` (Definition 1.51.4): an object
whose tensor product with every projective `P` is naturally isomorphic to `P^{**}`, and
which is fixed by the double-dual functor. -/
class HasDistinguishedInvertibleData where
  distinguished : C
  doubleDual_iso_tensor : ∀ (P : C) [Projective P],
    Nonempty (doubleDual P ≅ distinguished ⊗ P)
  doubleDual_self : Nonempty (doubleDual distinguished ≅ distinguished)

end CategoryTheory
