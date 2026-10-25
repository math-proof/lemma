/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/MonoidalBiexact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.SimpleRing.Field
import Mathlib.RingTheory.Artinian.Module
import Mathlib.CategoryTheory.Subobject.ArtinianObject
import Mathlib.RingTheory.Idempotents
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Tactic.CategoryTheory.Slice
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Theorem.v1.Atlas.TensorCategories.code.UnitSemisimplicity.MonoidalBiexact.Part3
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
