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
public import Theorem.v1.Atlas.TensorCategories.code.UnitSemisimplicity.MonoidalBiexact.Part3
@[expose] public section

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category CategoryTheory.Limits

universe v u w


noncomputable section

namespace TensorCategories

/-- Any abelian rigid monoidal preadditive braided category is monoidally biexact.
The proof uses duality adjunctions to deduce that left/right tensoring preserves
monomorphisms and epimorphisms, and combines this with the nondegeneracy lemma above. -/
noncomputable instance monoidalBiexact_of_rigidCategory
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
    [MonoidalPreadditive C] [RigidCategory C] [BraidedCategory C] : MonoidalBiexact C where
  whiskerRight_mono := fun {X Y} f _inst Z => by
    have adj := tensorRightAdjunction (HasLeftDual.leftDual Z) Z
    haveI := adj.rightAdjoint_preservesLimits
    haveI : (tensorRight Z).PreservesMonomorphisms :=
      preservesMonomorphisms_of_preservesLimitsOfShape _
    exact (tensorRight Z).map_mono f
  whiskerLeft_mono := fun Z {X Y} f _inst => by
    have adj := tensorLeftAdjunction Z (HasRightDual.rightDual Z)
    haveI := adj.rightAdjoint_preservesLimits
    haveI : (tensorLeft Z).PreservesMonomorphisms :=
      preservesMonomorphisms_of_preservesLimitsOfShape _
    exact (tensorLeft Z).map_mono f
  whiskerRight_epi := fun {X Y} f _inst Z => by
    have adj := tensorRightAdjunction Z (HasRightDual.rightDual Z)
    haveI := adj.leftAdjoint_preservesColimits
    haveI : (tensorRight Z).PreservesEpimorphisms :=
      preservesEpimorphisms_of_preservesColimitsOfShape _
    exact (tensorRight Z).map_epi f
  whiskerLeft_epi := fun Z {X Y} f _inst => by
    have adj := tensorLeftAdjunction (HasLeftDual.leftDual Z) Z
    haveI := adj.leftAdjoint_preservesColimits
    haveI : (tensorLeft Z).PreservesEpimorphisms :=
      preservesEpimorphisms_of_preservesColimitsOfShape _
    exact (tensorLeft Z).map_epi f
  isZero_of_tensorObj_self_isZero := isZero_of_tensorSelf_isZero

end TensorCategories
end
