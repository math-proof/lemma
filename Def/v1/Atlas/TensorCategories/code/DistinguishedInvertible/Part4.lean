/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DistinguishedInvertible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
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
public import Theorem.Category.Atlas.v1.TensorCategories.code.InvertibleObjects
public import Theorem.Category.Atlas.v1.TensorCategories.code.PivotalSpherical
public import Structure.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
public import Def.v1.Atlas.TensorCategories.code.CategoricalFreeness.Part2
public import Def.v1.Atlas.TensorCategories.code.DistinguishedInvertible.Part3

@[expose] public section
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category Limits TensorCategories

universe v u


namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]


/-- Build a pivotal structure on `C` from a family of double-dual isomorphisms on
projective objects together with a `HasDoubleDualExtension` instance. -/
@[reducible] noncomputable def pivotalFromProjectiveDoubleDual
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    [HasDoubleDualExtension C]
    (hDoubleDual : ∀ (P : C) [Projective P], Nonempty (doubleDual P ≅ P)) :
    PivotalCategory C where
  pivotalIso := HasDoubleDualExtension.extend_pivotalIso hDoubleDual
  tensorCoherenceIso := HasDoubleDualExtension.extend_tensorCoherenceIso hDoubleDual
  naturality := HasDoubleDualExtension.extend_pivotalIso_natural hDoubleDual
  monoidality := HasDoubleDualExtension.extend_monoidality hDoubleDual
  dimUnit := HasDoubleDualExtension.extend_dimUnit hDoubleDual

end CategoryTheory
