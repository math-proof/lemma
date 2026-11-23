/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/MonoidalBiexact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.SimpleRing.Field
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.CategoryTheory.Subobject.ArtinianObject
public import Mathlib.RingTheory.Idempotents
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.Tactic.CategoryTheory.Slice
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Class.v1.Atlas.TensorCategories.code.UnitSemisimplicity.MonoidalBiexact
@[expose] public section

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category CategoryTheory.Limits

universe v u w


noncomputable section

namespace TensorCategories

section TensorNondegenProof

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
  [MonoidalPreadditive C] [RigidCategory C] [BraidedCategory C]

/-- Right tensoring by an object preserves zero morphisms in a monoidal preadditive
category, supplying the `PreservesZeroMorphisms` instance for `tensorRight`. -/
instance tensorRight_preservesZeroMorphisms (Y : C) :
    (tensorRight Y).PreservesZeroMorphisms where
  map_zero _ _ := MonoidalPreadditive.zero_whiskerRight

/-- Left tensoring by an object preserves zero morphisms in a monoidal preadditive
category, supplying the `PreservesZeroMorphisms` instance for `tensorLeft`. -/
instance tensorLeft_preservesZeroMorphisms (Y : C) :
    (tensorLeft Y).PreservesZeroMorphisms where
  map_zero _ _ := MonoidalPreadditive.whiskerLeft_zero

end TensorNondegenProof
end TensorCategories
end
