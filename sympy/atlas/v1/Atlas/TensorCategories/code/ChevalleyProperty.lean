/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ChevalleyProperty.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.SemisimpleMultitensor
import Lemma.Category.Atlas.v1.TensorCategories.code.SemisimpleMultitensor

set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

section ChevalleyProperty

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

/-- A monoidal category `C` has the Chevalley property if the tensor product of two
semisimple objects is again semisimple (so the full subcategory of semisimple objects is a
monoidal subcategory). -/
class HasChevalleyProperty : Prop where
  tensor_semisimple : ∀ (X Y : C),
    IsSemisimpleObject C X → IsSemisimpleObject C Y → IsSemisimpleObject C (X ⊗ Y)

/-- Definition 1.31.1 (named restatement): the Chevalley property for a tensor category. -/
def Definition_1_31_1_ChevalleyProperty : Prop :=
  HasChevalleyProperty C

/-- Definition 1.31.1: the Chevalley property for a tensor category, expressed as a
proposition. -/
def Definition_1_31_1 : Prop :=
  HasChevalleyProperty C

end ChevalleyProperty

section Pointed

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

/-- A monoidal category is pointed in this Atlas formulation if every simple object has a
tensor inverse, i.e. is invertible. -/
class IsPointedTensorCategory : Prop where
  simple_has_inverse : ∀ (X : C) [Simple X],
    ∃ (Y : C), Nonempty (X ⊗ Y ≅ 𝟙_ C) ∧ Nonempty (Y ⊗ X ≅ 𝟙_ C)

/-- Helper for Proposition 1.31.2: a pointed tensor category has the Chevalley property. -/
end Pointed

section TensorBiproductDist

end TensorBiproductDist

section Pointed2

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [MonoidalPreadditive C] [HasFiniteBiproducts C]

/-- Proposition 1.31.2: A pointed tensor category has the Chevalley property. -/
end Pointed2

section SemisimpleChevalley

end SemisimpleChevalley

section LoewyLength

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

/-- A length-`n` semisimple filtration of an object `X`: a tuple of `n` semisimple objects
intended as the associated graded pieces of a filtration of `X`. -/
structure SemisimpleFiltration (X : C) (n : ℕ) where
  gradedPiece : Fin n → C
  gradedPiece_semisimple : ∀ i, IsSemisimpleObject C (gradedPiece i)

/-- Abstract data witnessing the existence of a Loewy length function on `C`: every object
admits some semisimple filtration of positive length, filtrations are functorial in tensor
products with multiplicative compatible length, and biproducts of semisimple objects are
semisimple. -/
structure LoewyLengthData where
  hasSemisimpleFiltration : C → ℕ → Prop
  hasSemisimpleFiltration_dec : ∀ (X : C), DecidablePred (hasSemisimpleFiltration X)
  hasSemisimpleFiltration_exists : ∀ (X : C), ∃ n, hasSemisimpleFiltration X n
  hasSemisimpleFiltration_pos : ∀ (X : C) (n : ℕ),
    hasSemisimpleFiltration X n → 1 ≤ n
  toFiltration : ∀ (X : C) (n : ℕ),
    hasSemisimpleFiltration X n → SemisimpleFiltration C X n
  filtration_tensor :
    ∀ (X Y : C) (m n : ℕ) (_ : m ≥ 1) (_ : n ≥ 1)
    (fX : SemisimpleFiltration C X m) (fY : SemisimpleFiltration C Y n),
    ∃ (candidateGradedPieces : Fin (m + n - 1) → C),

      (∀ (r : Fin (m + n - 1)),
        ∃ (k : ℕ) (pairs : Fin k → C) (hb : HasBiproduct pairs),
          (∀ p, ∃ (i : Fin m) (j : Fin n),
            pairs p = fX.gradedPiece i ⊗ fY.gradedPiece j) ∧
          Nonempty (candidateGradedPieces r ≅ @biproduct _ _ _ _ pairs hb)) ∧

      ((∀ r, IsSemisimpleObject C (candidateGradedPieces r)) →
        hasSemisimpleFiltration (X ⊗ Y) (m + n - 1))
  semisimple_biproduct : ∀ {k : ℕ} (f : Fin k → C) (hb : HasBiproduct f),
    (∀ i, IsSemisimpleObject C (f i)) →
    IsSemisimpleObject C (@biproduct _ _ _ _ f hb)

variable {C}

/-- The Loewy length `Lw(X)` of an object `X`, defined as the smallest `n` for which a
semisimple filtration of length `n` exists. -/
def LoewyLengthData.loewyLength (LD : LoewyLengthData C) (X : C) : ℕ :=
  @Nat.find _ (LD.hasSemisimpleFiltration_dec X) (LD.hasSemisimpleFiltration_exists X)

/-- In a semisimple category every object is already semisimple, so the Loewy length data
is trivially given by length `1` filtrations. -/
def loewyLengthDataOfSemisimple [IsSemisimpleCategory C] : LoewyLengthData C where
  hasSemisimpleFiltration := fun _ n => n ≥ 1
  hasSemisimpleFiltration_dec := fun _ => inferInstance
  hasSemisimpleFiltration_exists := fun _ => ⟨1, le_refl 1⟩
  hasSemisimpleFiltration_pos := fun _ _ h => h
  toFiltration := fun X n _ =>
    { gradedPiece := fun _ => X
      gradedPiece_semisimple := fun _ => IsSemisimpleCategory.semisimple X }
  filtration_tensor := fun X Y m n hm hn fX fY => by
    have hmn : m + n - 1 ≥ 1 := by omega

    set T := fX.gradedPiece ⟨0, by omega⟩ ⊗ fY.gradedPiece ⟨0, by omega⟩

    let pairs : Fin 1 → C := fun _ => T
    refine ⟨fun _ => T,
      fun r => ⟨1, pairs, inferInstance,
        fun _ => ⟨⟨0, by omega⟩, ⟨0, by omega⟩, rfl⟩,
        ⟨(biproductUniqueIso pairs).symm⟩⟩,
      fun _ => hmn⟩
  semisimple_biproduct := fun _ _ _ => IsSemisimpleCategory.semisimple _

/-- Tensor-product compatibility for a coradical-style Loewy length: the filtration is a
"Hopf algebra filtration" in the sense of Corollary 1.31.5 if `loewyLength (X ⊗ Y)` is
controlled by the sum of the Loewy lengths of `X` and `Y`. -/
structure IsHopfAlgebraFiltration (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasZeroMorphisms C] [HasChevalleyProperty C]
    (LD : LoewyLengthData C) : Prop where
  filtration_tensor_compat :
    ∀ (X Y : C) (i j : ℕ),
      LD.loewyLength X ≤ i → LD.loewyLength Y ≤ j →
      LD.loewyLength (X ⊗ Y) ≤ i + j

/-- A Hopf algebra filtration is "full" if it is also preserved by taking right duals,
matching `S(H_i) = H_i` in Corollary 1.31.5. -/
structure IsFullHopfAlgebraFiltration (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasZeroMorphisms C] [HasChevalleyProperty C]
    (LD : LoewyLengthData C) : Prop extends IsHopfAlgebraFiltration C LD where
  dual_preserves_filtration :
    ∀ (X : C) [HasRightDual X] (n : ℕ),
      LD.loewyLength X ≤ n ↔ LD.loewyLength (HasRightDual.rightDual (X := X)) ≤ n

/-- The Loewy length data for `C` coming from the coradical filtration in a pointed tensor
category with the Chevalley property. -/
end LoewyLength

end CategoryTheory
