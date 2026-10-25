/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Structure.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.PivotalSpherical
import Theorem.v1.Atlas.TensorCategories.code.SemisimpleMultitensor.Part5
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v u


noncomputable section

namespace CategoryTheory

section UnitSemisimple

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

section DualityAux

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- Functoriality of right duals on isomorphisms: an iso `V ≅ W` gives `Wᘁ ≅ Vᘁ` via right adjoint
mates. -/
def rightDualIsoOfIso {V W : C} (i : V ≅ W) : Wᘁ ≅ Vᘁ where
  hom := (i.hom)ᘁ
  inv := (i.inv)ᘁ
  hom_inv_id := by rw [← comp_rightAdjointMate]; simp
  inv_hom_id := by rw [← comp_rightAdjointMate]; simp

/-- Functoriality of left duals on isomorphisms: an iso `V ≅ W` gives `ᘁW ≅ ᘁV` via left adjoint
mates. -/
def leftDualIsoOfIso {V W : C} (i : V ≅ W) :
    (ᘁW : C) ≅ (ᘁV : C) where
  hom := ᘁ(i.hom)
  inv := ᘁ(i.inv)
  hom_inv_id := by rw [← comp_leftAdjointMate]; simp
  inv_hom_id := by rw [← comp_leftAdjointMate]; simp

/-- Any object is isomorphic to the right dual of its own left dual, `V ≅ (ᘁV)ᘁ`, via the
uniqueness of right duals on the rigid pairings. -/
def isoRightDualOfLeftDual (V : C) : V ≅ (ᘁV : C)ᘁ :=
  rightDualIso (HasLeftDual.exact (Y := V)) (HasRightDual.exact (X := (ᘁV : C)))

end DualityAux

section CompatibleDuals

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- In a braided rigid category the right dual `Vᘁ` also forms an exact pairing with `V` on the
other side, obtained by transporting the canonical pairing through the braiding. -/
@[reducible]
def exactPairing_rightDual_of_braided [BraidedCategory C] (V : C) :
    ExactPairing (Vᘁ) V :=
  @BraidedCategory.exactPairing_swap C _ _ _ V Vᘁ HasRightDual.exact

/-- Given a compatible exact pairing `ExactPairing Vᘁ V`, the left and right duals of `V` are
canonically isomorphic, `ᘁV ≅ Vᘁ`. -/
def leftDualIsoRightDual_of_compatibleDuals (V : C) (ep : ExactPairing (Vᘁ) V) : (ᘁV : C) ≅ Vᘁ :=

  leftDualIso HasLeftDual.exact ep

/-- Given a compatible exact pairing `ExactPairing Vᘁ V`, the object `V` is canonically isomorphic
to its double right dual `(Vᘁ)ᘁ`. -/
def doubleDualIso (V : C) (ep : ExactPairing (Vᘁ) V) : V ≅ (Vᘁ)ᘁ :=
  rightDualIso ep HasRightDual.exact

end CompatibleDuals

section TransportExactPairing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Transport an exact pairing `ExactPairing X Y` along an isomorphism `X ≅ X'` of the left
component to obtain an exact pairing `ExactPairing X' Y`. -/
@[reducible] noncomputable def ExactPairing.ofIsoLeft {X X' Y : C}
    (ep : ExactPairing X Y) (f : X ≅ X') : ExactPairing X' Y where
  coevaluation' := η_ X Y ≫ (f.hom ▷ Y)
  evaluation' := (Y ◁ f.inv) ≫ ε_ X Y
  coevaluation_evaluation' := by
    rw [whiskerLeft_comp, comp_whiskerRight]
    simp only [Category.assoc]
    rw [associator_inv_naturality_middle_assoc Y f.hom Y]
    rw [← comp_whiskerRight_assoc (Y ◁ f.hom) (Y ◁ f.inv) Y,
        ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id, id_whiskerRight,
        Category.id_comp]
    exact ep.coevaluation_evaluation'
  evaluation_coevaluation' := by
    rw [comp_whiskerRight, whiskerLeft_comp]
    simp only [Category.assoc]
    rw [associator_naturality_left_assoc]
    rw [← whisker_exchange_assoc f.hom (Y ◁ f.inv)]
    rw [← whisker_exchange f.hom (ε_ X Y)]
    rw [← associator_naturality_right_assoc X Y f.inv]
    rw [← whisker_exchange_assoc (η_ X Y) f.inv]
    change (𝟙_ C) ◁ f.inv ≫ ep.coevaluation' ▷ X ≫ (α_ X Y X).hom ≫
      X ◁ ep.evaluation' ≫ f.hom ▷ (𝟙_ C) = _
    rw [reassoc_of% ep.evaluation_coevaluation']
    rw [leftUnitor_naturality_assoc, ← rightUnitor_inv_naturality]
    simp [Iso.inv_hom_id_assoc]

end TransportExactPairing
end UnitSemisimple
end CategoryTheory
end
